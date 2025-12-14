# Character Concatenation as Pure Mathematics

## The Core Insight

String concatenation is just arithmetic in disguise.

```
"a" + "a" = "aa"
```

But what IS this operation mathematically?

## The Representation

| Representation | Value |
|----------------|-------|
| Character 'a' | ASCII 97 |
| Binary (8-bit) | `01100001` |
| Hex | `0x61` |

When we "concatenate" two characters:

```
'a' ++ 'a' = "aa"
```

We're really doing:

```
[97] ++ [97] = [97, 97]     -- As a list of bytes
```

Or as a single 16-bit integer:

```
01100001 ++ 01100001 = 0110000101100001
                     = 0x6161
                     = 24929
```

## The Mathematical Operation

**Character concatenation is bit-shifting followed by addition (or OR).**

For two 8-bit characters `a` and `b`:

```
a ⊕ b = (a << 8) | b
      = (a × 2⁸) + b
      = (a × 256) + b
```

Example:
```
97 ⊕ 97 = (97 × 256) + 97
        = 24832 + 97
        = 24929
```

Verification: `0x61 << 8 = 0x6100`, then `0x6100 | 0x61 = 0x6161 = 24929` ✓

## Three Concatenation Operators

| Operator | Name | Example | Formula |
|----------|------|---------|---------|
| `⊕` | Binary concat | 97 ⊕ 97 = 24929 | a × 2⁸ + b |
| `\|\|` | Decimal concat | 97 \|\| 97 = 9797 | a × 10^(digits(b)) + b |
| `++` | List concat | [97] ++ [97] = [97, 97] | append |

The binary concat `⊕` is the "true" concatenation for fixed-width integers.

The decimal concat `||` is what humans think of as "putting numbers next to each other":
```
97 || 97 = 97 × 100 + 97 = 9797
```

## List vs Packed Integer

What's the difference between `[97, 97]` and `24929`?

**They encode the same information differently:**

| Form | Type | Memory | Random Access |
|------|------|--------|---------------|
| `[97, 97]` | List U8 | 2+ bytes + overhead | O(n) |
| `24929` | U16 | exactly 2 bytes | O(1) via shift/mask |

The packed integer is:
- More compact
- Faster to compare (one instruction)
- Limited by integer width (max 8 chars in u64)

The list is:
- Unbounded length
- More overhead per element
- Easier to manipulate

## Generalization

For n characters of 8 bits each:

```
c₀ ⊕ c₁ ⊕ ... ⊕ cₙ₋₁ = Σᵢ (cᵢ × 2^(8×(n-1-i)))
```

Example: "abc" = [97, 98, 99]
```
97 × 2¹⁶ + 98 × 2⁸ + 99 × 2⁰
= 97 × 65536 + 98 × 256 + 99
= 6357024 + 25088 + 99
= 6382179
= 0x616263
```

This is just the interpretation of bytes as a big-endian integer!

## Algebraic Properties

**Is `⊕` associative?**

Only if we track width! Consider:
```
(a ⊕ b) ⊕ c  vs  a ⊕ (b ⊕ c)
```

If `a, b, c` are all U8:
- `a ⊕ b` produces U16
- `(a ⊕ b) ⊕ c` produces U24

We need a type system that tracks bit-width, or work with arbitrary-precision integers.

**Identity element?**

There's no identity for `⊕` in fixed-width arithmetic. But conceptually:
- The empty string "" is identity for list concatenation
- The zero-width integer (if it existed) would be identity for `⊕`

**Is `⊕` commutative?**

No! `97 ⊕ 98 ≠ 98 ⊕ 97`
```
97 ⊕ 98 = 24930  (0x6162 = "ab")
98 ⊕ 97 = 25185  (0x6261 = "ba")
```

This matches our intuition: "ab" ≠ "ba"

## The Formal Verification Angle

We can PROVE properties about strings by proving properties about integers:

1. **Length**: `len(a ⊕ b) = len(a) + len(b)` (bit-width addition)
2. **Prefix**: `a` is prefix of `a ⊕ b` (high bits match)
3. **Suffix**: `b` is suffix of `a ⊕ b` (low bits match)
4. **Equality**: `s₁ = s₂ ↔ int(s₁) = int(s₂)` (integer equality)

No string library needed - it's just arithmetic!

## Implementation Sketch

```rust
/// Concatenate two ASCII bytes into a u16
fn concat_chars(a: u8, b: u8) -> u16 {
    ((a as u16) << 8) | (b as u16)
}

/// Extract first character from a u16 "string"
fn first_char(s: u16) -> u8 {
    (s >> 8) as u8
}

/// Extract second character from a u16 "string"
fn second_char(s: u16) -> u8 {
    (s & 0xFF) as u8
}
```

Properties to prove:
```
∀ a b. first_char(concat_chars(a, b)) = a
∀ a b. second_char(concat_chars(a, b)) = b
∀ a b. concat_chars(first_char(s), second_char(s)) = s  -- for valid 2-char strings
```

## The Deep Insight

**Strings are not a special data type. They are a VIEWING of integers.**

Just like:
- Floating point is a viewing of bits as (sign, exponent, mantissa)
- Colors are a viewing of u32 as (R, G, B, A)
- IP addresses are a viewing of u32 as (octet, octet, octet, octet)

Strings are a viewing of arbitrary-precision integers as sequences of character codes.

The "string library" is just the API for this viewing:
- Concatenation = shift and add
- Length = bit width / 8
- Indexing = shift and mask
- Comparison = integer comparison

## MVP Scope

For the minimal viable proof:

1. Define `concat_chars : U8 → U8 → U16` in Rust
2. Translate to Lean via Aeneas
3. Prove: `first_char(concat_chars a b) = a`
4. Prove: `second_char(concat_chars a b) = b`
5. Prove: `concat_chars a b = concat_chars c d ↔ a = c ∧ b = d`

This establishes the foundation. Everything else is generalization.
