# Bitvector Proof Journey: Constant-Time Comparison Verification

## Overview

This document captures the process of formally verifying a constant-time byte comparison function in Lean 4 using the Aeneas toolchain. The journey reveals interesting challenges at the intersection of systems programming, formal verification, and pure functional reasoning.

## The Goal

Prove properties about `ct_eq_bytes`, a constant-time comparison function that compares two 8-byte arrays without early exit (important for cryptographic applications to prevent timing attacks).

### The Rust Implementation

```rust
pub fn ct_eq_bytes(a: &[u8; 8], b: &[u8; 8]) -> bool {
    let mut acc: u8 = 0;
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    // ... all 8 bytes
    acc |= a[7] ^ b[7];
    acc == 0
}
```

### The Generated Lean Code (via Aeneas)

```lean
def constant_time.ct_eq_bytes
  (a : Array U8 8#usize) (b : Array U8 8#usize) : Result Bool := do
  let i ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize b 0#usize
  let i2 ← (↑(i ^^^ i1) : Result U8)
  let acc ← (↑(0#u8 ||| i2) : Result U8)
  -- ... continues for all 8 pairs
  ok (acc7 = 0#u8)
```

## The Core Challenge

**Problem**: Prove `ct_eq_bytes a a = ok true` (reflexivity)

This seems trivial: if both arrays are the same, each XOR should produce 0, OR-ing zeros gives 0, and `0 = 0` is true.

**But**: The generated Lean code binds array accesses separately:
```lean
let i ← a.index_usize 0#usize
let i1 ← a.index_usize 0#usize  -- Same call, different binding!
let i2 ← ok (i ^^^ i1)          -- i and i1 are different variables
```

Even though `i` and `i1` will have the same value at runtime, they are **syntactically different terms** in the proof context. The simplifier doesn't know `i = i1`.

## Timeline of Attempts

### Attempt 1: Direct Simp
```lean
theorem ct_eq_bytes_refl (a : Array U8 8#usize) :
    ct_eq_bytes a a = ok true := by
  unfold ct_eq_bytes
  simp only [U8.xor_self]  -- Doesn't apply! Terms are i ^^^ i1, not i ^^^ i
```
**Result**: `simp` reports the argument is unused - it can't match `i ^^^ i1` against `x ^^^ x`.

### Attempt 2: Extensionality
Tried using `ext` tactic to prove U8 equality via bitvector equality.
```lean
rw [U8.eq_equiv_bv_eq]
```
**Result**: Works for simple cases, but doesn't solve the binding problem.

### Attempt 3: Progress Tactic
Aeneas provides a `progress` tactic for stepping through monadic computations:
```lean
progress as ⟨ v0 ⟩
progress as ⟨ v0' ⟩
```
**Result**: Creates separate hypotheses for each binding, but still doesn't connect them.

### Attempt 4: The Breakthrough - Referential Transparency

**Key Insight**: In pure functional programming, identical expressions produce identical results. This is **referential transparency**.

The expression `a.index_usize 0#usize` called twice *must* return the same value (if it succeeds). We can formalize this:

```lean
theorem bind_same_twice {α β : Type} (f : Result α) (g : α → α → Result β) :
    (do let x ← f; let y ← f; g x y) = (do let x ← f; g x x) := by
  cases f <;> simp [bind_tc_ok, bind_tc_fail, bind_tc_div]
```

This lemma says: "binding the same computation twice and using both results is equivalent to binding once and using the result twice."

### The Final Proof

```lean
theorem ct_eq_bytes_refl (a : Array U8 8#usize) :
    ct_eq_bytes a a = ok true := by
  unfold ct_eq_bytes
  -- Fuse duplicate bindings: (let i ← f; let j ← f; i ^^^ j) becomes (let i ← f; i ^^^ i)
  simp only [bind_same_twice, U8.xor_self, U8.zero_or, toResult, bind_tc_ok]
  -- Now i ^^^ i = 0, and 0 ||| 0 = 0, so accumulator is 0
  simp only [decide_true_eq]
  -- Handle the array bounds checking
  progress as ⟨ _, _ ⟩  -- 8 times, once per index
  progress as ⟨ _, _ ⟩
  -- ...
```

## Helper Lemmas Required

### 1. Bitvector Operations on U8
```lean
@[simp] theorem U8.bv_xor (x y : U8) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl
@[simp] theorem U8.bv_or (x y : U8) : (x ||| y).bv = x.bv ||| y.bv := rfl
@[simp] theorem U8.bv_zero : (0#u8).bv = 0#8 := rfl
```

These expose the underlying `BitVec` operations so we can use Lean's bitvector lemmas.

### 2. XOR Properties
```lean
theorem U8.xor_self (a : U8) : a ^^^ a = 0#u8
theorem U8.zero_or (a : U8) : 0#u8 ||| a = a
```

### 3. Result Monad Laws
```lean
-- The three-constructor Result type (ok, fail, div)
theorem bind_tc_ok {α β} (x : α) (f : α → Result β) : (ok x >>= f) = f x
theorem bind_tc_fail {α β} (e : Error) (f : α → Result β) : (fail e >>= f) = fail e
theorem bind_tc_div {α β} (f : α → Result β) : (div >>= f) = div
```

### 4. The Key Lemma
```lean
theorem bind_same_twice {α β : Type} (f : Result α) (g : α → α → Result β) :
    (do let x ← f; let y ← f; g x y) = (do let x ← f; g x x)
```

## Completed: Full Correctness Proof

### The Forward Direction (ct_eq_bytes returns true → arrays are equal)

This required several additional lemmas:

#### OR Decomposition (Bit-Level Reasoning)
```lean
theorem Bool.or_eq_false_iff' (a b : Bool) : (a || b) = false ↔ a = false ∧ b = false

theorem U8.or_eq_zero_iff (a b : U8) : a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8
```

The OR lemma was proven by decomposing to individual bits using `BitVec.eq_of_getLsbD_eq` - a byte is 8 bits, OR is pointwise, and `false || false = false` for each bit.

#### XOR Implies Equality
```lean
theorem U8.xor_eq_zero_iff (a b : U8) : a ^^^ b = 0#u8 ↔ a = b
```

Proven by XORing both sides by `b`: if `a ^^^ b = 0`, then `a ^^^ b ^^^ b = 0 ^^^ b`, so `a = b`.

#### The Complete Theorem
```lean
theorem ct_eq_bytes_correct (a b : Array U8 8#usize) :
    ct_eq_bytes a b = ok true ↔ a = b
```

**Forward direction proof strategy**:
1. Unfold `ct_eq_bytes` and extract that result is `ok true`
2. This means the accumulator `acc7 = 0`
3. Repeatedly apply `U8.or_eq_zero_iff` to peel off each XOR from the chain
4. Get `a[i] ^^^ b[i] = 0` for each index
5. Apply `U8.xor_eq_zero_iff` to get `a[i] = b[i]`
6. Use array extensionality (`List.ext_getElem`) to conclude `a = b`

## Lessons Learned

### 1. Pure Functional Reasoning is Powerful
The `bind_same_twice` lemma encapsulates referential transparency. This is a fundamental property of pure functions that we take for granted but must explicitly prove in a theorem prover.

### 2. Monadic Code Obscures Equality
The do-notation creates separate bindings for syntactically identical expressions. This is semantically correct (the monad laws don't require them to be equal), but makes proofs harder.

### 3. Layer Your Proofs
- Bottom layer: BitVec lemmas (`BitVec.xor_self`, etc.)
- Middle layer: U8 lemmas that lift BitVec facts (`U8.xor_self`, etc.)
- Top layer: Algorithm-specific lemmas (`bind_same_twice`, `ct_eq_bytes_refl`)

### 4. The Aeneas Ecosystem
- `progress` tactic: Steps through monadic computations
- `scalar_tac`: Handles scalar arithmetic
- `@[progress]` attribute: Registers theorems for the progress tactic
- `bind_tc_ok/fail/div`: Result monad laws

### 5. Type Precision Matters
Lean distinguishes between `0#8`, `(0 : BitVec 8)`, and `0#UScalarTy.U8.numBits`. These are definitionally equal but sometimes require explicit annotation.

### 6. Bit-Level Decomposition
For bitwise operations, treating a byte as 8 individual booleans and reasoning pointwise is often the cleanest approach.

---

## Critical Caveats: What This Proof Does NOT Prove

### The Epistemic Boundary

This proof is **formally valuable** but may be **epistemically opaque** to humans. The 400+ line proof file contains lemmas that very few people will ever read or understand in full. This is not a bug - it's the nature of formal verification at scale.

**The proof is not an explanation. It is a load-bearing structure.**

### What We Actually Proved

The proof establishes a **very specific claim**:

> Given this generated Lean program (translated from Rust via Aeneas), the function `ct_eq_bytes` returns `ok true` if and only if the two input arrays are element-wise equal.

The constant-time argument is **syntactic, not semantic**:
- No conditionals in the generated code
- No early exits
- Fixed number of operations

### What We Did NOT Prove

1. **"No side channels"** - Only "no control-flow dependence on secret data"
2. **Hardware behavior** - Caches, branch prediction, microcode, speculative execution are not modeled
3. **Compiler correctness** - We trust Aeneas's translation
4. **Real-world timing** - The idealized model doesn't account for variable-time instructions

### Where Bugs Can Hide

| Layer | What Could Go Wrong |
|-------|---------------------|
| Statement | The theorem might not capture what we actually care about |
| Model | Aeneas's semantics might not match Rust's semantics |
| Proof Assistant | Lean's kernel could have a bug (~10k LOC trusted base) |
| Extraction | Compiling Lean/Rust to machine code could introduce issues |
| Hardware | CPU behavior might not match the operational model |

### The Layered Trust Model

```
L0: Hardware behavior        (not proven - trusted)
L1: Instruction semantics    (modeled in Aeneas)
L2: Rust semantics           (modeled in Aeneas)
L3: Aeneas translation       (trusted)
L4: Lean proof               (machine-checked)
L5: Security claim           (human interpretation)
```

Each layer has a small core that is audited socially, not proven absolutely.

### "Pentest Search Space is Zero"?

**This claim would be false.** What we CAN say:

> Under this formal model, there exists no input that causes the function to return a different result than element-wise array comparison.

The moment you say "cannot be pentested", you've left mathematics and entered rhetoric. Formal methods **reduce** attack surface. They do not annihilate reality.

### When Formal Proofs Become Useless

They become useless when:
- The property proven is not the property people care about
- The assumptions are undocumented
- The result is oversold
- Humans cannot tell what changed if the code changes

### The Real Value

What we're actually building is:
- A **machine-verifiable correctness invariant**
- That survives refactoring
- That blocks entire bug classes (incorrect comparison logic)
- That forces attackers out of one dimension (algorithmic correctness)

Humans don't understand bridges either. They trust them because the failure modes are constrained.

---

## The Honest Security Statement

**Formally Verified Claim:**

> The function `ct_eq_bytes` in the Aeneas-generated Lean model is extensionally equivalent to element-wise array equality. The generated code contains no data-dependent control flow.

**Assumptions:**
- Aeneas correctly models Rust semantics
- The Lean kernel is correct
- Hardware executes fixed-operation-count code in constant time (idealized)

**NOT Claimed:**
- Protection against microarchitectural side channels
- Constant-time execution on all hardware
- Security against all timing attacks

---

## Future Work

1. ~~Complete the OR lemma's forward direction~~ ✓
2. ~~Prove full correctness: `ct_eq_bytes a b = ok true ↔ a = b`~~ ✓
3. Generalize to arbitrary-length arrays (requires loops/recursion)
4. Formalize the "no data-dependent control flow" property as a separate theorem
5. Extend to `ct_eq_16` for 16-byte arrays
6. Prove properties about the UTF-8 parser
7. Connect to a more realistic hardware timing model

## Connection to Broader Research

This work demonstrates that:
- **Cryptographic implementations can be formally verified** at the algorithm level
- **Rust code can be translated to pure Lean** via Aeneas/Charon
- **Referential transparency enables powerful equational reasoning** even in effectful-looking code
- **The gap between runtime semantics and proof semantics** requires careful bridging
- **Formal proofs shift from explanations to infrastructure** at scale

The constant-time property is actually easier to verify than correctness here - it's **structural** (no branches in the generated code), while correctness requires algebraic reasoning about XOR and OR.

---

*Document created: December 2024*
*Last updated: December 2024 - Full correctness proof completed*
*Project: lean_experiment - Formally Verified Rust Library*
