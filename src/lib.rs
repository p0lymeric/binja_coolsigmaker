//!
//!	binja_coolsigmaker
//!
//! a cooler sigmaker for binja
//!
//! Copyright (C) 2023  unknowntrojan
//! This program is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Affero General Public License as published
//! by the Free Software Foundation, either version 3 of the License, or
//! (at your option) any later version.
//!
//! This program is distributed in the hope that it will be useful,
//! but WITHOUT ANY WARRANTY; without even the implied warranty of
//! MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//! GNU Affero General Public License for more details.
//!
//! You should have received a copy of the GNU Affero General Public License
//! along with this program.  If not, see <https://www.gnu.org/licenses/>.
//!

#![feature(iter_array_chunks)]
use std::borrow::Cow;
// use std::sync::atomic::Ordering;

use std::fmt::Display;
use std::ops::Range;
use std::str::FromStr;
// use std::sync::atomic::AtomicUsize;
use std::time::SystemTime;

use binary_search::{Direction, binary_search};
use binaryninja::binary_view::search::SearchQuery;
use binaryninja::segment::Segment;
use binaryninja::{
    architecture::Architecture,
    binary_view::{BinaryView, BinaryViewBase, BinaryViewExt},
    command::{self, Command, RangeCommand},
    settings::Settings,
};

use clipboard::ClipboardProvider;
// use coolfindpattern::PatternSearcher;
use iced_x86::{
    Code::{DeclareByte, DeclareDword, DeclareQword, DeclareWord},
    ConstantOffsets, FlowControl, Formatter, Instruction, NasmFormatter, OpKind,
};
// use rayon::prelude::IntoParallelRefIterator;
// use rayon::prelude::ParallelBridge;
use rayon::prelude::ParallelIterator;
use serde_json::json;
use strum::{Display, EnumIter, EnumMessage, EnumString, IntoEnumIterator, VariantNames};

type OwnedPattern = Vec<Option<u8>>;
type Pattern<'a> = &'a [Option<u8>];

#[derive(PartialEq, Debug)]
struct CreatePatternValue {
    unique_spanning_size: usize,
    pattern: OwnedPattern,
}

#[derive(EnumIter, VariantNames, EnumMessage, EnumString, Display)]
enum SignatureType {
    #[strum(message = "IDA-style signature with one ? wildcard per byte. (E9 ? ? ? ? 90)")]
    IDAOne,
    #[strum(message = "IDA-style signature with two ? wildcards per byte. (E9 ?? ?? ?? ?? 90)")]
    IDATwo,
    #[strum(message = "Rust-style signature. (0xE9, _, _, _, _, 0x90)")]
    Rust,
    #[strum(message = "CStr-style signature. (\"\\xE9\\x00\\x00\\x00\\x00\\x90\", \"x????x\")")]
    CStr,
}

impl Default for SignatureType {
    fn default() -> Self {
        Self::IDATwo
    }
}

struct SigMakerCommand;
struct SigFinderCommand;

#[derive(PartialEq, thiserror::Error, Debug)]
enum SignatureError {
    #[error(
        "pattern is not unique even at size of {0} bytes! we either hit the limit or would have broken a function boundary."
    )]
    NotUnique(u64),
    #[error("encountered an invalid instruction")]
    InvalidInstruction,
    #[error("unable to query instruction's segment")]
    InvalidSegment,
}

struct RustPattern<'a>(Cow<'a, OwnedPattern>);
struct IDAOnePattern<'a>(Cow<'a, OwnedPattern>);
struct IDATwoPattern<'a>(Cow<'a, OwnedPattern>);
struct CStrPattern<'a>(Cow<'a, OwnedPattern>);

impl<'a> core::fmt::Display for RustPattern<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            match x {
                Some(x) => write!(f, "{:#04X}", x)?,
                None => write!(f, "_")?,
            }

            if i + 1 != self.0.len() {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }
}

impl<'a> core::fmt::Display for IDAOnePattern<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            match x {
                Some(x) => write!(f, "{:02X}", x)?,
                None => write!(f, "?")?,
            }

            if i + 1 != self.0.len() {
                write!(f, " ")?;
            }
        }

        Ok(())
    }
}

impl<'a> core::fmt::Display for IDATwoPattern<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            match x {
                Some(x) => write!(f, "{:02X}", x)?,
                None => write!(f, "??")?,
            }

            if i + 1 != self.0.len() {
                write!(f, " ")?;
            }
        }

        Ok(())
    }
}

impl<'a> core::fmt::Display for CStrPattern<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"")?;

        for x in self.0.iter() {
            match x {
                Some(x) => write!(f, "\\x{:02X}", x)?,
                None => write!(f, "?")?,
            }
        }

        write!(f, "\" \"")?;

        for x in self.0.iter() {
            match x {
                Some(_) => write!(f, "x")?,
                None => write!(f, "?")?,
            }
        }

        write!(f, "\"")?;

        Ok(())
    }
}

impl FromSignature for OwnedPattern {}

trait FromSignature {
    fn from_signature(mut pattern: String, signature_type: SignatureType) -> Option<OwnedPattern> {
        tracing::info!("attempting to parse a {signature_type}-style signature! \"{pattern}\"");

        pattern = pattern.replace("\n", "");
        pattern = pattern.replace("\r", "");
        pattern = pattern.replace("\t", "");
        pattern = pattern.trim().to_string();

        pub fn parse_idaone(mut pattern: String) -> Option<OwnedPattern> {
            // E9 ? ? ? ? 90 90
            pattern = pattern.replace("?", "??");
            parse_idatwo(pattern)
        }

        fn parse_idatwo(mut pattern: String) -> Option<OwnedPattern> {
            // E9 ?? ?? ?? ?? 90 90
            pattern = pattern.replace(" ", "");

            pattern
                .chars()
                .array_chunks::<2>()
                .try_fold(OwnedPattern::new(), |mut acc, byte| {
                    if byte == ['?', '?'] {
                        acc.push(None);
                    } else {
                        let Ok(byte) = u8::from_str_radix(&format!("{}{}", byte[0], byte[1]), 16)
                        else {
                            tracing::error!("unable to parse pattern!");
                            return None;
                        };

                        acc.push(Some(byte));
                    }

                    Some(acc)
                })
        }

        fn parse_rust(mut pattern: String) -> Option<OwnedPattern> {
            // 0xE9, _, _, _, _, 0x90, 0x9
            pattern = pattern.replace(",", "");
            pattern = pattern.replace("0x", "");
            pattern = pattern.replace("_", "??");

            parse_idatwo(pattern)
        }

        fn parse_cstr(pattern: String) -> Option<OwnedPattern> {
            // "\xE9\x00\x00\x00\x90\x90" "x????xx"

            let parts = pattern.split(" ").collect::<Vec<_>>();

            if parts.len() != 2 {
                tracing::error!("unable to parse pattern!");
                return None;
            }

            let first_part = parts[0].trim().replace("\"", "");

            let first_part = first_part
                .split("\\x")
                .into_iter()
                .map(|x| {
                    if x == "" || x.len() < 2 {
                        vec![]
                    } else {
                        let byte = &x[..2];
                        let wildcards = x.len() - 2;

                        let wildcards = (0..wildcards)
                            .into_iter()
                            .map(|_| None)
                            .collect::<Vec<Option<u8>>>();

                        let mut result = vec![
                            u8::from_str_radix(&byte, 16)
                                .map_err(|x| {
                                    tracing::error!("unable to parse pattern!");
                                    x
                                })
                                .ok(),
                        ];

                        result.extend(wildcards);

                        result
                    }
                })
                .flatten()
                .collect::<Vec<_>>();

            let second_part = parts[1].trim().replace("\"", "");

            let mut pattern = OwnedPattern::new();

            for (byte, mask) in first_part.iter().zip(second_part.chars()) {
                match mask {
                    'x' => {
                        pattern.push(Some(byte.unwrap()));
                    }
                    '?' => {
                        pattern.push(None);
                    }
                    _ => {
                        tracing::error!("invalid char encountered!");
                    }
                }
            }

            Some(pattern)
        }

        match signature_type {
            SignatureType::IDAOne => parse_idaone(pattern),
            SignatureType::IDATwo => parse_idatwo(pattern),
            SignatureType::Rust => parse_rust(pattern),
            SignatureType::CStr => parse_cstr(pattern),
        }
    }
}

fn get_code(bv: &BinaryView) -> Vec<(u64, Vec<u8>)> {
    bv.segments()
        .into_iter()
        .filter(|segment| segment.executable() || segment.contains_code())
        .map(|segment| {
            let range = segment.address_range();
            let len = range.end.checked_sub(range.start);

            let Some(len) = len else {
                return (range.start, Vec::new());
            };

            if len == 0 {
                return (range.start, Vec::new());
            }

            let mut data = vec![0u8; len as usize];

            bv.read(&mut data, range.start);

            (range.start, data)
        })
        .collect()
}

fn get_instruction_pattern(
    bv: &BinaryView,
    start_addr: u64,
    instr: &Instruction,
    offsets: &ConstantOffsets,
    buf: &[u8],
    relocations: &[Range<u64>],
    include_operands: bool,
) -> Result<OwnedPattern, SignatureError> {
    let buf_instr = &buf[..instr.len()];
    let mut pattern = buf_instr.into_iter().map(|x| Some(*x)).collect::<OwnedPattern>();

    if instr.is_invalid() || matches!(
        instr.code(),
        DeclareByte | DeclareWord | DeclareDword | DeclareQword
    ) {
        Err(SignatureError::InvalidInstruction)?
    }

    // Mask RIP-relative displacements that land on data
    // Based off Sigga's maskOperandsSmart
    if !include_operands && offsets.has_displacement() {
        // TODO does this need to be varianted for x86/x86-64?
        // RIP is set to be based on BN's basis instead of iced-x86's default basis
        let target = instr.memory_displacement64();
        // tracing::info!("displacement to {:x}", target);
        if bv.offset_valid(target) & !bv.offset_executable(target) {
            for x in offsets.displacement_offset()
                ..offsets.displacement_offset() + offsets.displacement_size()
            {
                pattern[x] = None;
            }
        }
    }

    // Mask large immediates (>64 kiB) that land on data
    // Based off Sigga's maskOperandsSmart
    if !include_operands && (offsets.has_immediate() || offsets.has_immediate2()) {
        // tracing::info!("has immediate");
        let replace_imm = (0..instr.op_count()).any(|i| {
            if let Ok(imm) = instr.try_immediate(i as u32) {
                if imm > 0x10000 {
                    // tracing::info!("large immediate referencing {:x}", target);
                    if bv.offset_valid(imm) & !bv.offset_executable(imm) {
                        return true;
                    }
                }
            }
            return false;
        });

        if replace_imm && offsets.has_immediate() {
            for x in
                offsets.immediate_offset()..offsets.immediate_offset() + offsets.immediate_size()
            {
                pattern[x] = None;
            }
        }

        if replace_imm && offsets.has_immediate2()  {
            for x in
                offsets.immediate_offset2()..offsets.immediate_offset2() + offsets.immediate_size2()
            {
                pattern[x] = None;
            }
        }
    }

    // Mask all call/uncond jump/cond branch targets
    let is_branch = matches!(
        instr.flow_control(),
        FlowControl::Call
        | FlowControl::ConditionalBranch
        | FlowControl::IndirectBranch
        | FlowControl::IndirectCall
        | FlowControl::UnconditionalBranch
    );
    if is_branch {
        // iced-x86 may compute the offsets on a different basis than BN, but we don't need to know its computation
        if offsets.has_immediate() {
            for x in
                offsets.immediate_offset()..offsets.immediate_offset() + offsets.immediate_size()
            {
                pattern[x] = None;
            }
        }

        if offsets.has_immediate2()  {
            for x in
                offsets.immediate_offset2()..offsets.immediate_offset2() + offsets.immediate_size2()
            {
                pattern[x] = None;
            }
        }
    }

    // Mask offsets that are targeted by the relocation table
    let start_addr = start_addr as usize;
    for relocation in relocations {
        if (start_addr..(start_addr + instr.len())).contains(&(relocation.start as usize)) {
            let start_offset = relocation.start as usize - start_addr;
            let end_offset = relocation.end as usize - start_addr;
            for x in start_offset..end_offset {
                pattern[x] = None;
            }
        }
    }

    Ok(pattern)
}

fn find_patterns<'a>(
    _code_segments: &'a [(u64, Vec<u8>)],
    pattern: Pattern<'a>,
    bv: &BinaryView,
) -> impl ParallelIterator<Item = u64> + 'a {
    // fn find_patterns_internal<'a>(
    //     region: &'a [u8],
    //     pattern: Pattern<'a>,
    // ) -> impl Iterator<Item = usize> + 'a {
    //     PatternSearcher::new(region, pattern)
    // }

    // code_segments
    //     .par_iter()
    //     .map(|segment| {
    //         find_patterns_internal(&segment.1, pattern)
    //             .map(|x| x as u64 + segment.0)
    //             .par_bridge()
    //     })
    //     .flatten()

    // FIXME coolfindpattern appears to return incorrect results
    // WA is to use bv.search with a FlexHex string
    let pattern_string = pattern
        .iter()
        .map(|maybe_b| match maybe_b {
            Some(b) => format!("{:02X}", b).to_string(),
            None => "??".to_string()
        })
        .collect::<Vec<String>>()
        .join(" ")
    ;

    let mut results = vec![];
    bv.search(&SearchQuery::new(pattern_string), |addr, _data_buffer| {
        results.push(addr);
        true
    });
    rayon::iter::IntoParallelIterator::into_par_iter(results)
}

fn is_pattern_unique(_code_segments: &[(u64, Vec<u8>)], pattern: Pattern, bv: &BinaryView) -> bool {
    // let iter = find_patterns(code_segments, pattern);

    // let count = AtomicUsize::new(0);

    // iter.find_any(|_| {
    //     count.fetch_add(1, Ordering::Relaxed);
    //     count.load(Ordering::Relaxed) > 1
    // });

    // count.load(Ordering::Relaxed) == 1

    // FIXME coolfindpattern appears to return incorrect results
    // WA is to use bv.search with a FlexHex string
    let pattern_string = pattern
        .iter()
        .map(|maybe_b| match maybe_b {
            Some(b) => format!("{:02X}", b).to_string(),
            None => "??".to_string()
        })
        .collect::<Vec<String>>()
        .join(" ")
    ;

    let mut count = 0;
    bv.search(&SearchQuery::new(pattern_string), |_addr, _data_buffer| {
        count += 1;
        true
    });
    count == 1
}

fn yield_next_instruction(
    bv: &BinaryView,
    addr: u64,
    current_offset: u64,
    data_segment: &(u64, Vec<u8>),
    start_segment: &binaryninja::rc::Ref<Segment>,
    max_size: u64,
    relocations: &[Range<u64>],
    formatter: &mut NasmFormatter,
    include_operands: bool,
) -> Result<Option<OwnedPattern>, SignatureError> {
    let instr_addr = addr + current_offset;
    let instr_addr_rel = instr_addr - start_segment.address_range().start;

    let max_size_or_segment_end = std::cmp::min(
        max_size,
        data_segment.1.len() as u64 - (instr_addr - data_segment.0),
    );

    // frame the start of the next instruction
    // iced_x86 will just decode the first instruction so the slice can be open-ended
    let instr_bytes = &data_segment.1[instr_addr_rel as usize..];

    let mut decoder = iced_x86::Decoder::new(
        if let Some(arch) = bv.default_arch() {
            (arch.address_size() * 8) as u32
        } else {
            64
        },
        instr_bytes,
        0,
    );
    decoder.set_ip(instr_addr);

    let instr = decoder.decode();
    let offsets = decoder.get_constant_offsets(&instr);

    let instr_pattern = get_instruction_pattern(
        bv,
        addr + current_offset,
        &instr,
        &offsets,
        instr_bytes,
        &relocations,
        include_operands,
    )?;

    #[cfg(debug_assertions)]
    {
        let mut instr_string = String::new();
        formatter.format(&instr, &mut instr_string);
        tracing::info!(
            "{}: {}",
            instr_string,
            RustPattern(Cow::Borrowed(&instr_pattern))
        );
    }

    if current_offset + instr.len() as u64 >= max_size_or_segment_end {
        return Ok(None);
    }

    // check that we are not crossing function boundaries
    // the range we were in at the start is still the same range as we are currently scanning
    if !bv.functions_containing(addr as u64).iter().any(|func| {
        func.address_ranges().iter().any(|range| {
            range.start <= addr && range.end >= (instr_addr + instr.len() as u64) as u64
        })
    }) {
        return Ok(None);
    }

    Ok(Some(instr_pattern))
}

#[derive(Display)]
enum SearchStrategyKind {
    LinearSearch,
    BinarySearch,
}

fn create_pattern_internal(
    bv: &BinaryView,
    range: &Range<u64>,
    data: &[(u64, Vec<u8>)],
    include_operands: bool,
    search_strategy: SearchStrategyKind,
) -> Result<CreatePatternValue, SignatureError> {
    let time = SystemTime::now();

    let include_all_selected_instructions = get_include_all_selected_instructions(bv);

    // Patterns are constructed in three phases:
    // Phase I: Get the minimum pattern from range.start to uniquely identify the location in the executable. This is the minimum unique signature.
    // Phase II: Extend the minimum pattern until it covers [range.start, range.end - 1]. This is the minimum unique spanning signature.
    // Phase III: Extend the pattern until it is at least min_size wide or a function boundary is reached. This is the minimum size signature.

    let (addr, selection_size) = if include_all_selected_instructions {
        tracing::info!("creating pattern for address {:#04X}..={:#04X}", range.start, range.end - 1);
        (range.start, range.end - range.start)
    } else {
        tracing::info!("creating pattern for address {:#04X}", range.start);
        (range.start, 1)
    };

    let mut formatter = NasmFormatter::new();
    formatter.options_mut().set_rip_relative_addresses(true);

    let relocations = bv.relocation_ranges();

    let mut current_offset = 0u64;
    let mut current_pattern = OwnedPattern::default();

    let min_size = get_minimum_signature_size(bv);
    let max_size = get_maximum_signature_size(bv);

    let Some(start_segment) = bv.segment_at(addr as u64) else {
        Err(SignatureError::InvalidSegment)?
    };

    let data_segment = data
        .iter()
        .find(|segment| segment.0 == start_segment.address_range().start)
        .ok_or(SignatureError::InvalidSegment)?;

    #[cfg(debug_assertions)]
    tracing::info!("max sig size: {max_size}");

    // Phase I
    match search_strategy {
        SearchStrategyKind::LinearSearch => {
            let mut pattern_unique = false;

            while !pattern_unique {
                if let Some(instr_pattern) = yield_next_instruction(
                    bv, addr, current_offset, data_segment, &start_segment, max_size, &relocations, &mut formatter, include_operands,
                )? {
                    current_pattern.extend(&instr_pattern);
                    current_offset += instr_pattern.len() as u64;
                    pattern_unique = is_pattern_unique(&data, &current_pattern, bv);
                } else {
                    break;
                }
            }
        },
        SearchStrategyKind::BinarySearch => {
            // This algorithm will currently load all instructions up to maximum_signature_size before performing filtering,
            // which unnecessarily hurts performance with large values of maximum_signature_size
            // It could possibly be improved by preloading ~32 bytes and dynamically filling current_pattern during bisection as needed

            let mut instr_offsets = vec![];

            loop {
                if let Some(instr_pattern) = yield_next_instruction(
                    bv, addr, current_offset, data_segment, &start_segment, max_size, &relocations, &mut formatter, include_operands,
                )? {
                    current_pattern.extend(&instr_pattern);
                    instr_offsets.push((current_offset, instr_pattern.len()));
                    current_offset += instr_pattern.len() as u64;
                } else {
                    break;
                }
            }

            let ((_, _), (unique_instr, _)) =
                binary_search((0, ()), (instr_offsets.len() as _, ()), |instr| {
                    let instr = instr_offsets[instr];
                    let pat = &current_pattern[0..instr.0 as usize + instr.1];

                    #[cfg(debug_assertions)]
                    tracing::info!("{}", RustPattern(Cow::Borrowed(&pat.to_vec())));

                    match is_pattern_unique(&data, pat, bv) {
                        false => Direction::Low(()),
                        true => Direction::High(()),
                    }
                });

            let instr = instr_offsets[unique_instr.clamp(0, instr_offsets.len() - 1)];

            // FIXME slightly wasteful as phase II and III could add these instructions again
            current_offset = instr.0 + instr.1 as u64;
            current_pattern.drain(current_offset as usize..);
        },
    }

    // Phase II
    while current_pattern.len() < selection_size as usize {
        if let Some(instr_pattern) = yield_next_instruction(
            bv, addr, current_offset, data_segment, &start_segment, max_size, &relocations, &mut formatter, include_operands,
        )? {
            current_pattern.extend(&instr_pattern);
            current_offset += instr_pattern.len() as u64;
        } else {
            break;
        }
    }

    let remove_terminal_wildcards = get_remove_terminal_wildcards(bv);

    // Compute minimum unique spanning size, adjusting for the fact this implementation strips trailing wildcards
    let unique_spanning_size = if remove_terminal_wildcards {
        current_pattern
            .iter()
            .rposition(|x| x.is_some())
            .map_or(0, |i| i + 1)
    } else {
        current_pattern.len()
    };

    // Phase III
    while current_pattern.len() < min_size as usize {
        if let Some(instr_pattern) = yield_next_instruction(
            bv, addr, current_offset, data_segment, &start_segment, max_size, &relocations, &mut formatter, include_operands,
        )? {
            current_pattern.extend(&instr_pattern);
            current_offset += instr_pattern.len() as u64;
        } else {
            break;
        }
    }

    // Strip trailing None from the final pattern
    if remove_terminal_wildcards {
        while let Some(x) = current_pattern.last()
            && x.is_none()
        {
            current_pattern.pop();
        }
    }

    tracing::info!(
        "{} created pattern in {}ms",
        search_strategy.to_string().to_lowercase(), SystemTime::now().duration_since(time).unwrap().as_millis()
    );

    Ok(CreatePatternValue { unique_spanning_size, pattern: current_pattern })
}

fn create_pattern(bv: &BinaryView, range: &Range<u64>) -> Result<CreatePatternValue, SignatureError> {
    let include_operands = get_include_operands(bv);
    let data = get_code(bv);

    #[cfg(debug_assertions)]
    {
        let pattern = create_pattern_internal(bv, range, &data, include_operands, SearchStrategyKind::LinearSearch);
        let binsearch_pattern =
            create_pattern_internal(bv, range, &data, include_operands, SearchStrategyKind::BinarySearch);

        let _ = pattern
            .as_ref()
            .map(|pat| tracing::info!("{}", RustPattern(Cow::Borrowed(&pat.pattern))));

        let _ = binsearch_pattern
            .as_ref()
            .map(|pat| tracing::info!("{}", RustPattern(Cow::Borrowed(&pat.pattern))));

        if pattern.as_ref().unwrap() != binsearch_pattern.as_ref().unwrap() {
            tracing::error!("patterns dont match :(((");
        }
    }

    let pattern = if get_binary_search(bv) {
        create_pattern_internal(bv, range, &data, include_operands, SearchStrategyKind::BinarySearch)
    } else {
        create_pattern_internal(bv, range, &data, include_operands, SearchStrategyKind::LinearSearch)
    };

    let pattern = if !include_operands && matches!(pattern, Err(SignatureError::NotUnique(_))) {
        tracing::warn!(
            "unable to find a unique pattern that didn't include operands. trying again with operands!"
        );
        if get_binary_search(bv) {
            create_pattern_internal(bv, range, &data, true, SearchStrategyKind::BinarySearch)
        } else {
            create_pattern_internal(bv, range, &data, true, SearchStrategyKind::LinearSearch)
        }
    } else {
        pattern
    };

    if pattern
        .as_ref()
        .is_ok_and(|pat| !is_pattern_unique(&data, &pat.pattern, bv))
    {
        tracing::error!("signature not unique, cannot proceed!");
        return Err(SignatureError::NotUnique(
            pattern.map_or(0u64, |pat| pat.pattern.len() as u64),
        ));
    }

    pattern
}

fn emit_result(contents: String) {
    tracing::info!("{}", &contents);
    if let Err(e) = set_clipboard_contents(contents) {
        tracing::error!("unable to copy to clipboard: {}", e);
    }
}

fn set_clipboard_contents(contents: String) -> Result<(), Box<dyn std::error::Error>> {
    let mut ctx: clipboard::ClipboardContext = clipboard::ClipboardProvider::new()?;

    ctx.set_contents(contents)
}

fn get_clipboard_contents() -> Result<String, Box<dyn std::error::Error>> {
    let mut ctx: clipboard::ClipboardContext = clipboard::ClipboardProvider::new()?;

    ctx.get_contents()
}

fn get_minimum_signature_size(_bv: &BinaryView) -> u64 {
    Settings::new().get_integer("coolsigmaker.minimum_size")
}

fn get_maximum_signature_size(_bv: &BinaryView) -> u64 {
    Settings::new().get_integer("coolsigmaker.maximum_size")
}

fn get_include_all_selected_instructions(_bv: &BinaryView) -> bool {
    Settings::new().get_bool("coolsigmaker.include_all_selected_instructions")
}

fn get_include_operands(_bv: &BinaryView) -> bool {
    Settings::new().get_bool("coolsigmaker.include_operands")
}

fn get_binary_search(_bv: &BinaryView) -> bool {
    Settings::new().get_bool("coolsigmaker.binary_search")
}

fn get_remove_terminal_wildcards(_bv: &BinaryView) -> bool {
    Settings::new().get_bool("coolsigmaker.remove_terminal_wildcards")
}

fn get_signature_type(_bv: &BinaryView) -> SignatureType {
    SignatureType::from_str(Settings::new().get_string("coolsigmaker.sig_type").as_str())
        .map_err(|_| {
            tracing::error!("invalid value for coolsigmaker.sig_type! falling back to default!")
        })
        .unwrap_or(SignatureType::IDATwo)
}

fn register_settings() {
    fn register_setting<T>(
        settings: &Settings,
        name: &str,
        title: &str,
        description: &str,
        typ: &str,
        default: T,
        extra_properties: &[(&str, &serde_json::Value)],
    ) where
        T: core::fmt::Display + serde::Serialize,
    {
        let mut properties_val = json!({
            "title": title,
            "type": typ,
            "default": default,
            "description": description,
            "ignore": ["SettingsProjectScope", "SettingsResourceScope"],
        });

        let properties = properties_val.as_object_mut().unwrap();
        for (key, val) in extra_properties {
            properties.insert(key.to_string(), (*val).clone());
        }

        settings.register_setting_json(name, &properties_val.to_string());
    }

    fn register_enum_setting<T>(settings: &Settings, name: &str, title: &str, description: &str)
    where
        T: Display + EnumMessage + VariantNames + IntoEnumIterator + Default,
    {
        let enum_variants = T::VARIANTS;
        let enum_descriptions = T::iter()
            .map(|x| x.get_message().unwrap_or(""))
            .collect::<Vec<_>>();

        let properties = format!(
            r#"
		{{
			"title": "{title}",
			"type": "string",
			"default": "{}",
			"description": "{description}",
			"ignore": ["SettingsProjectScope", "SettingsResourceScope"],
			"enum": {},
			"enumDescriptions": {}
		}}
		"#,
            T::default(),
            serde_json::to_string(enum_variants).unwrap(),
            serde_json::to_string(&enum_descriptions).unwrap()
        );

        settings.register_setting_json(name, &properties);
    }

    let settings = Settings::new();

    settings.register_group("coolsigmaker", "CoolSigMaker");

    register_setting::<bool>(
        &settings,
        "coolsigmaker.include_all_selected_instructions",
        "Include All Selected Instructions",
        "When enabled, the signature includes all instructions in a ranged selection. When disabled, only includes the first instruction in a selection.",
        "boolean",
        true,
        &[],
    );

    register_setting::<bool>(
        &settings,
        "coolsigmaker.include_operands",
        "Include Operands",
        "Include immediate operands that aren't memory-relative or relocated when creating signatures. This results in smaller, but potentially more fragile, signatures. If no unique signature can be generated without operands, we fall back to including them.",
        "boolean",
        false,
        &[],
    );

    register_setting::<bool>(
        &settings,
        "coolsigmaker.binary_search",
        "Use Binary Search",
        "Use a binary search to determine instruction uniqueness. For small binaries, this will be slower than the default, while for bigger binaries it might be faster. It starts scanning at half the maximum signature size. There is no heuristic implemented to automatically determine this yet.",
        "boolean",
        false,
        &[],
    );

    register_setting::<u64>(
        &settings,
        "coolsigmaker.maximum_size",
        "Maximum Signature Size",
        "The maximum size the signature will accumulate before giving up.",
        "number",
        64,
        &[
            ("minValue", &json!(0)),
            // i32::MAX is one before when the widget changes from a spinner to a hex input box
            ("maxValue", &json!(i32::MAX)),
        ],
    );

    register_setting::<u64>(
        &settings,
        "coolsigmaker.minimum_size",
        "Minimum Signature Size",
        "The minimum size the signature will accumulate. Signatures are constructed to uniquely span the selection, then extended until they reach minimum size or the function boundary.",
        "number",
        0,
        &[
            ("minValue", &json!(0)),
            // i32::MAX is one before when the widget changes from a spinner to a hex input box
            ("maxValue", &json!(i32::MAX))
        ],
    );

    register_setting::<bool>(
        &settings,
        "coolsigmaker.remove_terminal_wildcards",
        "Remove Terminal Wildcards",
        "When enabled, removes any wildcards at the end of a generated signature. When disabled, a signature always ends on an instruction boundary.",
        "boolean",
        true,
        &[],
    );

    register_enum_setting::<SignatureType>(
        &settings,
        "coolsigmaker.sig_type",
        "Signature Type",
        "The signature type to use for creating and finding signatures",
    );
}

#[test]
fn test_patterns() {
    // .clone() code smell..... but this eliminates calling .unwrap() and then comparing by reference, whatever.
    let test_pattern = vec![Some(0xE9), None, None, None, None, Some(0x90), Some(0x90)];

    assert_eq!(
        OwnedPattern::from_signature(String::from("E9 ? ? ? ? 90 90"), SignatureType::IDAOne),
        Some(test_pattern.clone())
    );

    assert_eq!(
        OwnedPattern::from_signature(String::from("E9 ?? ?? ?? ?? 90 90"), SignatureType::IDATwo),
        Some(test_pattern.clone())
    );

    assert_eq!(
        OwnedPattern::from_signature(
            String::from("0xE9, _, _, _, _, 0x90, 0x90"),
            SignatureType::Rust
        ),
        Some(test_pattern.clone())
    );

    assert_eq!(
        OwnedPattern::from_signature(
            String::from(r#""\xE9\x00??\x00\x90\x90" "x????xx""#),
            SignatureType::CStr
        ),
        Some(test_pattern.clone())
    );
}

impl RangeCommand for SigMakerCommand {
    fn action(&self, bv: &BinaryView, range: Range<u64>) {
        match create_pattern(bv, &range) {
            Ok(create_pattern_value) => {
                let pattern_len = create_pattern_value.pattern.len();

                let pattern: Box<dyn core::fmt::Display> = match get_signature_type(bv) {
                    SignatureType::IDAOne => Box::new(IDAOnePattern(Cow::Owned(create_pattern_value.pattern))),
                    SignatureType::IDATwo => Box::new(IDATwoPattern(Cow::Owned(create_pattern_value.pattern))),
                    SignatureType::Rust => Box::new(RustPattern(Cow::Owned(create_pattern_value.pattern))),
                    SignatureType::CStr => Box::new(CStrPattern(Cow::Owned(create_pattern_value.pattern))),
                };

                if create_pattern_value.unique_spanning_size != pattern_len {
                    tracing::info!("minimum unique spanning length is {} bytes, extended to {} bytes", create_pattern_value.unique_spanning_size, pattern_len);
                } else {
                    tracing::info!("minimum unique spanning length is {} bytes", create_pattern_value.unique_spanning_size);
                }
                emit_result(format!("{}", pattern));
            }
            Err(e) => {
                tracing::error!("unable to create pattern! {e}");
            }
        }
    }

    fn valid(&self, bv: &BinaryView, range: Range<u64>) -> bool {
        // assert there is a function at the specified range start, otherwise disable the menu option.
        // the pattern creation process will make sure we stay within a valid function
        // within the range and past range.end.
        !bv.functions_containing(range.start).is_empty()
    }
}

impl Command for SigFinderCommand {
    fn action(&self, bv: &BinaryView) {
        let Ok(sig) = get_clipboard_contents() else {
            tracing::error!("unable to get signature from clipboard!");
            return;
        };

        let time = SystemTime::now();

        let data = get_code(bv);

        let Some(pattern) = OwnedPattern::from_signature(sig, get_signature_type(bv)) else {
            tracing::error!("failed to parse pattern.");
            return;
        };

        find_patterns(&data, &pattern, bv)
            .for_each(|occurrence| tracing::info!("found signature at {:#04X}", occurrence));

        tracing::info!(
            "scan finished in {}ms.",
            SystemTime::now().duration_since(time).unwrap().as_millis()
        );
    }

    fn valid(&self, _bv: &BinaryView) -> bool {
        true
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn CorePluginInit() -> bool {
    binaryninja::tracing_init!("CoolSigMaker");

    // TODO: (maybe) if signature not found, maybe go back a few instructions and attempt to create a signature with an offset.
    // TODO: introduce a setting for "dumb" searches, where we also search non-executable segments for uniqueness, incase the user doesn't want to check the segments before scanning them.
    // TODO: make a fancy regex to distinguish signature types automagically (without accidental mismatches occurring)

    tracing::info!("binja_coolsigmaker by unknowntrojan loaded!");
    tracing::info!("say hello to the little ninja in your binja");

    #[cfg(debug_assertions)]
    std::panic::set_hook(Box::new(|info| {
        let string = format!(
            "{}\n{:#?}\n{}",
            info,
            info,
            std::backtrace::Backtrace::force_capture()
        );

        // #[cfg(debug_assertions)]
        let _ = std::fs::write("E:\\log.txt", &string);

        tracing::info!("{}", &string);
    }));

    register_settings();

    command::register_command_for_range(
        "CSM - Create Signature from Address",
        "Creates a Signature from the currently selected address",
        SigMakerCommand {},
    );

    command::register_command(
        "CSM - Find Signature",
        "Finds a signature in the binary.",
        SigFinderCommand {},
    );

    true
}
