# Ideas

## Formally Verified String Library

Strings are just integers (ASCII/UTF-8) on top of bits. Aeneas doesn't support string literals, but we could build a formally verified string library from first principles using `List U8` or `Vec<u8>`. Prove properties like: valid UTF-8 encoding, string equality, substring operations, all without relying on unverified stdlib.

## Character Concatenation as Pure Math (MVP)

String concatenation is arithmetic in disguise. `'a' ⊕ 'a' = 97 ⊕ 97 = 24929` where `a ⊕ b = (a << 8) | b = a × 256 + b`. Strings are not a special data type - they are a *viewing* of integers as sequences of character codes. The MVP: prove `first_char(concat_chars a b) = a` and `second_char(concat_chars a b) = b` for a simple 2-char concatenation. This establishes that "string operations" are just bit manipulation with proofs.

See: `ideas/CHARACTER_CONCATENATION.md`

## Password-Protected Secret

A minimal security example: a function that returns a secret number only when given the correct password. Password is `List U8` with length 8-10. Prove: (1) correct password always returns secret, (2) wrong password never returns secret, (3) no timing side-channels in comparison. This demonstrates the SecurityDuality concept - a pentester cannot find an exploit because the proof closes the search space.

See: `LeanExperiment/SecurityDuality.lean`

## Verified Calabi-Yau Toolkit

Formally verified string theory computations. Prove that genetic algorithm operations (fitness, mutation, selection) preserve Calabi-Yau mathematical invariants. If professional physicists use verified code, the mathematical guarantees transfer to their results.

See: `INITIAL_EXPLORATION.md`

## Security Duality Framework

Pentesting is inverted property testing. Tests search for confirmation (`∀x. P(x)`), pentests search for violation (`∃x. ¬P(x)`). A formal proof makes the attacker's search space empty - not unexplored, but nonexistent.

See: `LeanExperiment/SecurityDuality.lean`, `INITIAL_EXPLORATION.md`
