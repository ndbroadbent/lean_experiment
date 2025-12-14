# Bitvector Proof TODO: Roadmap to 100% Verified Password CLI

This document tracks all remaining work to fully verify the password/secret stdin CLI sample program with zero `sorry`s.

---

## Current Status

### Completed
- [x] `ct_eq_bytes` reflexivity: `ct_eq_bytes a a = ok true`
- [x] `ct_eq_bytes` full correctness: `ct_eq_bytes a b = ok true <-> a = b`
- [x] Helper lemmas: `U8.xor_self`, `U8.or_eq_zero_iff`, `U8.xor_eq_zero_iff`
- [x] Bit-level decomposition via `BitVec.eq_of_getLsbD_eq`
- [x] Array extensionality via `List.ext_getElem`
- [x] `bind_same_twice` referential transparency lemma

### Not Started
- [ ] Password module proofs
- [ ] Larger array comparison proofs (16, 32 bytes)
- [ ] UTF-8 parser proofs
- [ ] Formal constant-time property
- [ ] CLI stdin model (may not be possible)

---

## Phase 1: Password Module Proofs

### 1.1 check_password Correctness
**File**: `ConstantTimeProofs.lean` (new section) or `PasswordProofs.lean`

```lean
-- check_password uses ct_eq_bytes internally
theorem check_password_correct (input : Array U8 8#usize) :
    password.check_password input = ok true <-> input = password.PASSWORD
```

**Strategy**:
- Unfold `check_password` definition
- Apply `ct_eq_bytes_correct`
- The proof should be nearly trivial given `ct_eq_bytes_correct`

**Difficulty**: Easy

### 1.2 reveal_secret Security Properties

```lean
-- Correct password reveals the secret
theorem reveal_secret_correct_password :
    password.reveal_secret password.PASSWORD = ok (some password.SECRET)

-- Wrong password reveals nothing
theorem reveal_secret_wrong_password (input : Array U8 8#usize)
    (h : input != password.PASSWORD) :
    password.reveal_secret input = ok none
```

**Strategy**:
- Unfold `reveal_secret` and `check_password`
- Use `ct_eq_bytes_correct` for the forward direction
- Use decidability of `input = PASSWORD` for case split

**Difficulty**: Easy-Medium

### 1.3 reveal_secret_result Equivalence

```lean
-- Result variant is equivalent to Option variant
theorem reveal_secret_result_equiv (input : Array U8 8#usize) :
    (password.reveal_secret_result input = ok (core.result.Result.Ok s)) <->
    (password.reveal_secret input = ok (some s))
```

**Difficulty**: Easy

---

## Phase 2: Extend to Larger Arrays

### 2.1 ct_eq_16 Correctness

**File**: `ConstantTimeProofs.lean`

```lean
theorem ct_eq_16_correct (a b : Array U8 16#usize) :
    constant_time.ct_eq_16 a b = ok true <-> a = b
```

**Strategy**:
- Same approach as `ct_eq_bytes_correct`
- 16 cases instead of 8
- Consider macro/tactic to automate repetitive case structure

**Difficulty**: Medium (tedious, but straightforward)

### 2.2 ct_eq_32 Correctness

```lean
theorem ct_eq_32_correct (a b : Array U8 32#usize) :
    constant_time.ct_eq_32 a b = ok true <-> a = b
```

**Strategy**:
- Same as above, 32 cases
- Strongly consider automation

**Difficulty**: Medium (more tedious)

### 2.3 Generalization (Optional - Advanced)

```lean
-- A generic constant-time comparison for arbitrary length
-- This would require proving properties about loops/recursion
-- in the Aeneas-generated code
theorem ct_eq_n_correct {n : Usize} (a b : Array U8 n) :
    ct_eq_n a b = ok true <-> a = b
```

**Status**: Requires loop-based implementation in Rust first, then Aeneas translation with `partial_fixpoint`

**Difficulty**: Hard

---

## Phase 3: UTF-8 Parser Proofs

### 3.1 sequence_length Correctness

**File**: `Utf8Proofs.lean` (new)

```lean
-- ASCII bytes (0x00-0x7F) have sequence length 1
theorem sequence_length_ascii (b : U8) (h : b.val < 128) :
    utf8.sequence_length b = ok 1#u8

-- 2-byte sequences (0xC0-0xDF lead byte)
theorem sequence_length_2byte (b : U8) (h : 192 <= b.val /\ b.val <= 223) :
    utf8.sequence_length b = ok 2#u8

-- etc. for 3-byte and 4-byte
```

**Difficulty**: Medium

### 3.2 is_continuation Correctness

```lean
theorem is_continuation_spec (b : U8) :
    utf8.is_continuation b = ok true <-> (b.val &&& 192 = 128)
```

**Difficulty**: Easy-Medium

### 3.3 Validation Theorems

```lean
-- A valid 1-byte sequence is ASCII
theorem validate_1byte_iff_ascii (b : U8) :
    utf8.validate_1byte b = ok true <-> b.val < 128

-- 2-byte validation
theorem validate_2byte_spec (b0 b1 : U8) :
    utf8.validate_2byte b0 b1 = ok true <->
    (sequence_length b0 = 2 /\ is_continuation b1)
```

**Difficulty**: Medium

### 3.4 CodePoint Round-Trip (Advanced)

```lean
-- Create a code point and read it back
theorem code_point_1_roundtrip (b : U8) (h : b.val < 128) :
    do let cp <- utf8.code_point_1 b
       utf8.code_point_byte0 cp
    = ok b
```

**Difficulty**: Medium

---

## Phase 4: Formal Constant-Time Property

### 4.1 Define Data-Independent Control Flow

**Concept**: The "constant-time" property means the control flow doesn't depend on secret data. We can formalize this structurally.

```lean
-- A function has no data-dependent branches if the generated Lean code
-- contains no `if` statements whose conditions depend on the inputs

-- For ct_eq_bytes, we can observe:
-- 1. All array accesses are unconditional
-- 2. All XOR/OR operations are unconditional
-- 3. Only the final `acc == 0` comparison produces a branch,
--    but that branch only happens at the END (after all data is processed)

-- We could formalize this as:
inductive ConstantTimeExpr : Result Bool -> Prop where
  | pure : ConstantTimeExpr (ok b)
  | bind_array : (forall i, ConstantTimeExpr (f i)) ->
                 ConstantTimeExpr (do let x <- arr.index i; f x)
  -- etc.
```

**Status**: Research-level - may not be achievable in current framework

**Difficulty**: Very Hard (research problem)

### 4.2 Structural Proof (Lighter Weight)

```lean
-- Document that ct_eq_bytes has no early exit
-- This is a "proof by inspection" that we can formalize as:

-- The function always performs exactly 8 XORs and 8 ORs
-- regardless of input values

-- We can prove this by showing the function never returns
-- fail for in-bounds inputs, and the number of operations is fixed
theorem ct_eq_bytes_total (a b : Array U8 8#usize) :
    exists r, ct_eq_bytes a b = ok r
```

**Difficulty**: Easy (already implicit in correctness proof)

---

## Phase 5: End-to-End CLI Verification (Limits)

### 5.1 What CAN Be Verified

The password checking logic:
- `check_password(input) = true <-> input = PASSWORD`
- `reveal_secret(input) = Some(SECRET) <-> input = PASSWORD`
- Constant-time structure of comparison (no early exit)

### 5.2 What CANNOT Be Verified (with current tools)

**stdin/stdout behavior**: The Rust `main.rs` currently doesn't use the password module. To add a CLI:

```rust
// Hypothetical main.rs addition
fn main() {
    let mut input = [0u8; 8];
    std::io::stdin().read_exact(&mut input).unwrap();
    match password::reveal_secret(&input) {
        Some(secret) => println!("Secret: {:?}", secret),
        None => println!("Access denied"),
    }
}
```

**Why it can't be verified**:
1. Aeneas doesn't model `std::io` - no translation to Lean
2. stdin/stdout are side effects, not pure functions
3. The "real" security depends on OS/hardware/timing behavior

### 5.3 Verification Boundary

```
+--------------------------------------------------+
|  VERIFIED (Lean proofs)                          |
|  - ct_eq_bytes correctness                       |
|  - check_password correctness                    |
|  - reveal_secret correctness                     |
|  - Constant-time structure (no branches)         |
+--------------------------------------------------+
                    |
                    v (trust boundary)
+--------------------------------------------------+
|  TRUSTED (not verified)                          |
|  - Aeneas translation correctness                |
|  - Rust compiler correctness                     |
|  - OS/libc behavior                              |
|  - Hardware timing                               |
+--------------------------------------------------+
```

---

## Phase 6: Documentation & Methodology

### 6.1 Update BITVECTOR_PROOF_JOURNEY.md
- [x] Document completed proofs
- [x] Add epistemic caveats section
- [x] Layered trust model
- [x] Honest security statement

### 6.2 Create Proof Patterns Guide (Optional)

Document reusable patterns:
- Bit-level decomposition via `BitVec.eq_of_getLsbD_eq`
- OR chain decomposition
- Array extensionality
- `bind_same_twice` for referential transparency

---

## Priority Order

1. **Phase 1** (Password proofs) - Highest value, builds on existing work
2. **Phase 2.1** (ct_eq_16) - Natural extension
3. **Phase 3.1-3.2** (UTF-8 basics) - Interesting standalone
4. **Phase 2.2** (ct_eq_32) - If automation is developed
5. **Phase 3.3-3.4** (UTF-8 advanced) - More complex
6. **Phase 4** (Constant-time formal) - Research-level

---

## Metrics

| Component | Lines of Rust | Lines of Lean Proof | Status |
|-----------|---------------|---------------------|--------|
| ct_eq_bytes | 15 | ~300 | Done |
| check_password | 3 | ~20 (est) | TODO |
| reveal_secret | 7 | ~50 (est) | TODO |
| ct_eq_16 | 18 | ~350 (est) | TODO |
| ct_eq_32 | 42 | ~600 (est) | TODO |
| UTF-8 parser | ~100 | ~500+ (est) | TODO |

---

## Notes

### Zero-Sorry Goal
To achieve "zero sorrys" for the password verification:
1. Complete Phase 1 (password proofs)
2. Ensure `ConstantTimeProofs.lean` builds with `lake build`
3. Ensure `PasswordProofs.lean` builds (if separate)

### What "100% Verified" Means Here
- All Lean proof files compile without `sorry`
- All theorems proven in Lean's kernel
- Trust assumptions documented clearly

### What It Does NOT Mean
- Real-world security guarantee
- Protection against all side channels
- Correct behavior on all hardware

---

*Document created: December 2024*
*Last updated: December 2024*
*Project: lean_experiment - Formally Verified Rust Library*
