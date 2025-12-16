# AcerFur's Proof: Analysis for Lean Formalization

## The Setup

For primes p=7, q=11, r=13 with a=pq=77, b=pr=91, c=qr=143:
- Window: [5935, 6077] (143 consecutive integers centered at 6006)
- Need: abc | xyz where abc = p²q²r²
- Equivalently: v_p(xyz) ≥ 2, v_q(xyz) ≥ 2, v_r(xyz) ≥ 2

## The Core Combinatorial Argument

### Key Fact
6006 is the ONLY number in [5935, 6077] divisible by two or more of {7, 11, 13}.

Why? The next multiples of each pairwise product:
- 77: 5929, **6006**, 6083 — only 6006 in range
- 91: 5915, **6006**, 6097 — only 6006 in range
- 143: 5863, **6006**, 6149 — only 6006 in range

### The Counting Argument

We need v_p(xyz) ≥ 2, v_q(xyz) ≥ 2, v_r(xyz) ≥ 2.

Think of this as needing **6 total "hits"** (2 per prime).

Each number x, y, z contributes valuations to the three primes:
- A "single-prime" number (divisible by exactly one of p,q,r) contributes 1 hit
- A "double-prime" number (divisible by exactly two) contributes 2 hits
- A "triple-prime" number (divisible by all three) contributes 3 hits

**Constraint**: At most ONE of x, y, z can be a double/triple (only 6006 qualifies).

### Case 1: None of x, y, z is divisible by two primes

Each contributes to at most 1 prime.
Maximum hits: 1 + 1 + 1 = 3 < 6. **Impossible.**

### Case 2: Exactly one (say z = 6006) is divisible by multiple primes

- z = 6006 = 2 × 3 × 7 × 11 × 13 contributes (1, 1, 1) — that's 3 hits
- x contributes to at most 1 prime — that's ≤ 1 hit
- y contributes to at most 1 prime — that's ≤ 1 hit

Maximum hits: 3 + 1 + 1 = 5 < 6. **Impossible.**

### Conclusion

No valid triple exists. QED.

## Note on Squared Primes

AcerFur's original proof mentions needing p², q², r² in the window. This is a different perspective on the same constraint:

- If we could use squared primes (like 49, 121, 169), a single number could contribute v=2 to one prime
- But 169 > 143, so no multiple of 13² exists in any 143-length window
- The counting argument above is more direct: we simply can't accumulate enough hits

## Lean Formalization Strategy

1. **Prove 6006 is the only multi-prime number** (decidable check)
2. **Prove the pigeonhole**: with ≤1 multi-prime contributor, max hits = 5 < 6
3. **Conclude**: no valid triple exists

The pigeonhole step requires formalizing:
- A "contribution" type: how many of {p, q, r} divide a number
- The sum of contributions from 3 numbers
- The constraint that ≤1 has contribution ≥ 2
