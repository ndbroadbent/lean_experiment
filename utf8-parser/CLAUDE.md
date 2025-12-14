# UTF-8 Parser - Formally Verified UTF-8 Byte Parsing

Self-contained project for verifying UTF-8 sequence detection and validation.

## What This Proves

1. **Classification**: `sequence_length` correctly identifies byte types
2. **Validation**: `validate_Nbyte` accepts exactly valid sequences
3. **Round-trip**: `code_point` constructors and accessors are inverses

## Build Commands

```bash
# Rust
cd rust && cargo test

# Generate Lean from Rust
cd rust && charon && aeneas -backend lean utf8_parser.llbc

# Build Lean proofs
lake build
```

## Files

```
rust/src/
└── utf8.rs            # sequence_length, is_continuation, validate_*, CodePoint

Utf8Parser.lean        # Aeneas-generated (DO NOT EDIT)
Utf8Proofs.lean        # Formal proofs
```

## UTF-8 Encoding Reference

```
0xxxxxxx              → 1-byte (ASCII, 0x00-0x7F)
110xxxxx 10xxxxxx     → 2-byte (0xC0-0xDF lead, 0x80-0xBF continuation)
1110xxxx 10xxxxxx × 2 → 3-byte (0xE0-0xEF lead)
11110xxx 10xxxxxx × 3 → 4-byte (0xF0-0xF7 lead)
```

## Proof Layers

```
Layer 0: Bit-level
├── U8.bv_and, BitVec.getLsbD properties

Layer 1: Classification
├── sequence_length_total, sequence_length_ascii, is_continuation_spec

Layer 2: Validation
├── validate_2byte_correct, validate_3byte_correct, validate_4byte_correct

Layer 3: Round-trip
├── code_point_N_bytes_roundtrip
```
