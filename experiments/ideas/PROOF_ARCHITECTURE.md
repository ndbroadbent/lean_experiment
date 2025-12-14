# Proof Architecture: Building Layered, Composable Formal Proofs

This document captures the methodology for building clean, modular formal proofs rather than one giant global mess.

---

## Naming Conventions

In mathematics and proof assistants, these terms are **social labels**, not strict technical categories:

| Term | Meaning | Usage |
|------|---------|-------|
| **Lemma** | A helper fact used to prove something else | "Plumbing" - not the main result |
| **Proposition** | A standalone result, not necessarily "big" | Medium-importance facts |
| **Theorem** | A result you want to highlight as important | The "headline" results |
| **Corollary** | Follows quickly from a theorem | Trivial consequences |
| **Claim** | An intermediate step inside a proof | Often local, inside a `have` |
| **Auxiliary lemma** | Same as lemma, explicitly "plumbing" | Infrastructure |

In Lean/Coq/Isabelle, `theorem` / `lemma` / `proposition` are usually **synonyms** with different pretty-printing intent. The type system doesn't treat them differently.

---

## Proof Organization Patterns

### Pattern 1: Modules and Namespaces

Build a library file (or several), prove things once, then `import` elsewhere.

```
ConstantTimeProofs.lean    -- Foundation: XOR, OR, bit-level lemmas
  └── exports: U8.xor_self, U8.or_eq_zero_iff, ct_eq_bytes_correct

PasswordProofs.lean        -- Builds on ConstantTimeProofs
  └── imports ConstantTimeProofs
  └── exports: check_password_correct, reveal_secret_security

Utf8Proofs.lean            -- Independent module
  └── exports: sequence_length_ascii, code_point_roundtrip
```

The **interface** is the set of exported definitions + theorems.

### Pattern 2: Abstract Interfaces via Typeclasses/Structures

Prove generic facts once, then "plug in" implementations.

```lean
-- Abstract interface for constant-time equality
class ConstantTimeEq (α : Type) where
  eq : α → α → Bool
  -- Functional correctness
  spec : eq x y = true ↔ x = y
  -- Structural constant-time property
  structural_ct : NoBranches eq

-- Instance for 8-byte arrays
instance : ConstantTimeEq (Array U8 8#usize) where
  eq := ct_eq_bytes
  spec := ct_eq_bytes_correct
  structural_ct := ct_eq_bytes_no_branches

-- Instance for 16-byte arrays
instance : ConstantTimeEq (Array U8 16#usize) where
  eq := ct_eq_16
  spec := ct_eq_16_correct
  structural_ct := ct_eq_16_no_branches

-- Generic theorem: works for ANY ConstantTimeEq instance
theorem secure_compare [ConstantTimeEq α] (secret input : α) :
    ConstantTimeEq.eq secret input = true ↔ secret = input :=
  ConstantTimeEq.spec
```

### Pattern 3: Functor-like Composition

Build proofs that compose: "if A satisfies P and B satisfies Q, then A∘B satisfies R."

This is common in security:

```
┌─────────────────────────────────────────────────────────────────┐
│ Layer 4: Whole-System Property                                  │
│   "No timing leak under this threat model"                      │
│   Theorem: system_timing_secure                                 │
├─────────────────────────────────────────────────────────────────┤
│ Layer 3: Protocol Step                                          │
│   "Reject on mismatch, accept on match"                         │
│   Theorem: reveal_secret_correct                                │
├─────────────────────────────────────────────────────────────────┤
│ Layer 2: Construction                                           │
│   "MAC comparison is correct and constant-time"                 │
│   Theorem: check_password_correct                               │
├─────────────────────────────────────────────────────────────────┤
│ Layer 1: Primitive                                              │
│   "ct_eq_bytes compares arrays correctly"                       │
│   Theorem: ct_eq_bytes_correct                                  │
├─────────────────────────────────────────────────────────────────┤
│ Layer 0: Bit-level Foundation                                   │
│   "XOR, OR, bitwise properties"                                 │
│   Lemmas: U8.xor_self, U8.or_eq_zero_iff, etc.                  │
└─────────────────────────────────────────────────────────────────┘
```

Each layer's theorems **compose** by referencing theorems from the layer below.

### Pattern 4: Refinement Layers

Prove an abstract spec, then refine to an implementation.

```
┌─────────────────────────────────────────────────────────────────┐
│ Spec Model (Pure Math)                                          │
│   compare_spec : List Byte → List Byte → Bool                   │
│   compare_spec xs ys = (xs = ys)                                │
├─────────────────────────────────────────────────────────────────┤
│ Impl Model (Aeneas-generated Lean)                              │
│   ct_eq_bytes : Array U8 8 → Array U8 8 → Result Bool           │
├─────────────────────────────────────────────────────────────────┤
│ Refinement Theorem                                              │
│   ct_eq_bytes a b = ok (compare_spec a.toList b.toList)         │
└─────────────────────────────────────────────────────────────────┘
```

Everything above can depend only on the **spec**, and you need only **one refinement proof** to connect to real code.

---

## Local Subproofs vs Reusable Facts

### Local Subproofs

Use `have` / `let` / local `lemma` inside one theorem:

```lean
theorem big_theorem : P := by
  -- Local helper, not exported
  have helper : Q := by
    ...
  -- Use helper
  exact some_tactic helper
```

### Reusable Facts

Export as module-level lemmas/theorems:

```lean
-- In BitLevelLemmas.lean
theorem U8.xor_self (a : U8) : a ^^^ a = 0#u8 := by ...

-- In ConstantTimeProofs.lean
import BitLevelLemmas

theorem ct_eq_bytes_refl : ct_eq_bytes a a = ok true := by
  ...
  simp [U8.xor_self]  -- Use imported lemma
```

### Reusable Clusters

Bundle related theorems in a module with an abstract interface:

```lean
-- In ConstantTime.lean
namespace ConstantTime

structure EqSpec (α : Type) where
  eq : α → α → Result Bool
  correct : ∀ a b, eq a b = ok true ↔ a = b
  total : ∀ a b, ∃ r, eq a b = ok r

def Array8Spec : EqSpec (Array U8 8#usize) := {
  eq := ct_eq_bytes,
  correct := ct_eq_bytes_correct,
  total := ct_eq_bytes_total
}

end ConstantTime
```

---

## Property Vocabulary for Security

For "proof interface" composition, be explicit about the **property vocabulary** you export:

### 1. Functional Correctness Spec

```lean
-- The function computes what we expect
theorem ct_eq_bytes_correct (a b : Array U8 8#usize) :
    ct_eq_bytes a b = ok true ↔ a = b
```

### 2. Totality / Non-Failure

```lean
-- The function never panics for valid inputs
theorem ct_eq_bytes_total (a b : Array U8 8#usize) :
    ∃ r, ct_eq_bytes a b = ok r
```

### 3. Constant-Time Spec (Structural)

At different model levels:

**Source-level** (what we can easily prove):
```lean
-- No data-dependent branches in the generated Lean code
-- This is a "proof by inspection" - the code has no `if` on secret data
def NoBranches (f : α → α → Result Bool) : Prop :=
  -- The function's control flow is independent of input values
  -- (formalized as: same sequence of operations for all inputs)
  sorry -- Research-level to fully formalize
```

**Structural observation**:
```lean
-- The generated code performs exactly 8 XORs, 8 ORs, 1 compare
-- regardless of input values. This is visible in the Lean code.
-- No early exit is possible.
```

**IR-level** (would need Aeneas model):
```lean
-- The MIR/LLVM representation has no secret-dependent branches
```

**Instruction-level** (outside our model):
```lean
-- All instructions are constant-time on target hardware
-- This is ASSUMED, not proven
```

### 4. Refinement Bridge

```lean
-- Connects abstract spec to concrete implementation
theorem refinement :
    impl_function x = ok (spec_function x)
```

### 5. Composition Lemmas

```lean
-- How properties compose through function calls
theorem composition_preserves_ct
    (f : α → Result β) (g : β → Result γ)
    (hf : ConstantTime f) (hg : ConstantTime g) :
    ConstantTime (fun x => do let y ← f x; g y)
```

---

## Recommended File Structure

```
lean_experiment/
├── BitLevelLemmas.lean       -- Layer 0: Foundational bit operations
│   └── U8.xor_self, U8.or_eq_zero_iff, bind_same_twice
│
├── ConstantTimeProofs.lean   -- Layer 1: Primitive proofs
│   └── ct_eq_bytes_correct, ct_eq_bytes_refl
│
├── PasswordProofs.lean       -- Layer 2: Construction proofs
│   └── check_password_correct, reveal_secret_security
│
├── Utf8Proofs.lean           -- Independent module
│   └── sequence_length_*, code_point_roundtrip
│
├── SecurityInterfaces.lean   -- Abstract interfaces (typeclasses)
│   └── ConstantTimeEq, SecureCompare
│
└── ideas/
    ├── PROOF_ARCHITECTURE.md   -- This document
    ├── BITVECTOR_PROOF_JOURNEY.md -- Case study
    └── BITVECTOR_PROOF_TODO.md -- Roadmap
```

---

## Current Project Layers

For our password verification project:

```
Layer 0: Bit-level Foundation (ConstantTimeProofs.lean)
├── U8.xor_self : a ^^^ a = 0
├── U8.or_eq_zero_iff : a ||| b = 0 ↔ a = 0 ∧ b = 0
├── U8.xor_eq_zero_iff : a ^^^ b = 0 ↔ a = b
├── bind_same_twice : referential transparency
└── Bool.or_eq_false_iff' : bit-level OR decomposition

Layer 1: Primitive (ConstantTimeProofs.lean)
├── ct_eq_bytes_refl : ct_eq_bytes a a = ok true
└── ct_eq_bytes_correct : ct_eq_bytes a b = ok true ↔ a = b

Layer 2: Construction (TODO: PasswordProofs.lean)
├── check_password_correct : check_password p = ok true ↔ p = PASSWORD
└── reveal_secret_correct : reveal_secret p = ok (some SECRET) ↔ p = PASSWORD
     reveal_secret_wrong : p ≠ PASSWORD → reveal_secret p = ok none

Layer 3: System Property (TODO)
├── password_security : Only correct password reveals secret
└── timing_security : No timing side-channel (structural argument)

Trust Boundary (not proven, assumed):
├── Aeneas translation correctness
├── Rust compiler correctness
├── Hardware constant-time execution
└── OS/runtime behavior
```

---

## Anti-Patterns to Avoid

### 1. Giant Monolithic Proof Files
**Bad**: 1000-line proof file with everything mixed together
**Good**: Separate files for each layer, clear imports

### 2. Inline Everything
**Bad**: Reprove `U8.xor_self` inside every theorem that needs it
**Good**: Prove once, export, import where needed

### 3. No Abstraction
**Bad**: Hardcode `Array U8 8#usize` everywhere
**Good**: Use typeclasses for generic proofs

### 4. Unclear Property Vocabulary
**Bad**: Vague claims about "security"
**Good**: Explicit: correctness, totality, constant-time (with model specified)

### 5. No Trust Boundary
**Bad**: Claim "fully verified, unhackable"
**Good**: Document exactly what is proven and what is assumed

---

## The Honest Security Statement Template

```markdown
## Formally Verified Claim

> [Precise mathematical statement of what was proven]

## Assumptions

- [List of trusted components: Aeneas, Lean kernel, etc.]
- [Model limitations: what the formal model doesn't capture]

## NOT Claimed

- [Explicit list of things NOT proven]
- [Threat models NOT covered]

## Layer Dependencies

- [What lower-layer theorems this result depends on]
- [What trust assumptions propagate up]
```

---

---

## Lean's Caching System: Incremental Proof Compilation

Lean doesn't re-check proofs every time you run it. It compiles each file into a binary artifact and only rechecks files whose dependencies changed.

### How Caching Works

```
Source Files          Compiled Artifacts
─────────────         ──────────────────
BitLevelLemmas.lean → BitLevelLemmas.olean
                      ├── definitions
                      ├── theorems
                      ├── proof terms
                      └── dependency hashes

ConstantTimeProofs.lean → ConstantTimeProofs.olean
  imports BitLevelLemmas    (only recompiles if BitLevelLemmas changed)
```

If nothing upstream changed, Lean **trusts the `.olean`** and moves on.

### Granularity: File-Level, Not Lemma-Level

**Important**: Caching is per-file, not per-lemma.

| Change | Effect |
|--------|--------|
| Change anything in a file | That file recompiles |
| Change a file's exports | Downstream files may recompile |
| Change only comments | Usually no recompile needed |
| Rebuild without changes | Uses cached `.olean` |

**Implication**: Structure matters.

```
Good Structure:
├── BitLevelLemmas.lean      ← Stable, rarely changes
├── ResultMonadLaws.lean     ← Stable foundation
├── ConstantTimeSpec.lean    ← Interface, changes rarely
├── ConstantTimeImpl.lean    ← Implementation details
└── Experiments.lean         ← Unstable, experimental

Bad Structure:
└── Everything.lean          ← Any change recompiles everything
```

### What Triggers Recompilation

**Will recompile**:
- File content changes
- Imported file's exported interface changes
- Dependency hash changes

**Won't recompile**:
- Only comments change (usually)
- Rebuild without touching files
- Dependencies unchanged

### Practical Patterns for Large Proofs

#### 1. Split Files by Stability

```
Stable (change rarely):
  BitVecLemmas.lean
  ResultMonadLaws.lean

Semi-stable (interface fixed, proofs may evolve):
  ConstantTimeSpec.lean

Volatile (actively developing):
  ConstantTimeImpl.lean
  Experiments.lean
```

#### 2. Minimize Exports

```lean
-- In BitLevelLemmas.lean
namespace BitLevel

-- Exported (part of interface)
theorem U8.xor_self (a : U8) : a ^^^ a = 0#u8 := ...

-- Private helper (not exported)
private theorem helper_lemma : ... := ...

end BitLevel
```

Use namespaces to avoid accidental dependency growth.

#### 3. Abstract Early

```lean
-- Prove generic lemma once
theorem xor_self_generic [XorOp α] [Zero α] (a : α) : a ^^^ a = 0 := ...

-- Specialize later (cheap, uses existing proof)
theorem U8.xor_self := xor_self_generic (α := U8)
theorem U16.xor_self := xor_self_generic (α := U16)
```

#### 4. Avoid Rewriting Public Definitions

```lean
-- BAD: Changing this forces downstream recompilation
def ct_eq_bytes ... := ...  -- Don't modify once stable

-- GOOD: Add lemmas instead of changing definitions
theorem ct_eq_bytes_new_property : ... := ...
```

### Kernel Trust and Reuse

When Lean loads a `.olean`, it does **not** re-run the proof. It trusts:
- The kernel type-checked it once
- The hash matches
- The trusted kernel hasn't changed

**Result**: Once proven, a theorem is effectively "cached forever" unless you invalidate it.

### Critical Caveat: Caching Proofs, Not Meaning

Lean caches *proofs*, not *models*.

If you:
- Change the definition of `ConstantTime`
- Change the semantics of `Result`
- Change the extraction pipeline

Lean will happily reuse proofs that no longer match your **intent**, only your **types**.

```lean
-- Original
def is_secure := no_timing_leaks ∧ no_memory_leaks

-- Later changed to
def is_secure := no_timing_leaks  -- Removed memory check!

-- Old proofs still "work" because types match
-- But meaning has drifted!
```

**Implication**:
- Interfaces are everything
- Naming is not semantics
- Document what definitions MEAN, not just what they TYPE

### Stable Proof Interface Design

To keep cached proofs meaningful:

#### 1. Lock Down Definitions

```lean
-- Mark as irreducible once stable
@[irreducible]
def ct_eq_bytes := ...

-- Now proofs can't depend on internal structure
-- Only on exported lemmas
```

#### 2. Semantic Versioning for Proof Modules

```
BitLevelLemmas.lean v1.0
  - U8.xor_self
  - U8.or_eq_zero_iff

  Breaking changes require version bump:
  - Changing theorem statements
  - Removing exports
  - Changing definition semantics
```

#### 3. Golden Theorems

Designate certain theorems as "the interface":

```lean
-- These are THE public interface. Do not change.
-- Everything else is implementation detail.

/-- The definitive correctness spec for ct_eq_bytes -/
@[simp] theorem ct_eq_bytes_correct :
    ct_eq_bytes a b = ok true ↔ a = b := ...

/-- The definitive totality spec -/
theorem ct_eq_bytes_total :
    ∃ r, ct_eq_bytes a b = ok r := ...
```

#### 4. Test Theorems

Add "sanity check" theorems that would break if meaning drifts:

```lean
-- If this stops compiling, something fundamental changed
example : ct_eq_bytes ⟨[1,2,3,4,5,6,7,8]⟩ ⟨[1,2,3,4,5,6,7,8]⟩ = ok true := rfl

example : ct_eq_bytes ⟨[1,2,3,4,5,6,7,8]⟩ ⟨[0,0,0,0,0,0,0,0]⟩ = ok false := rfl
```

### Measuring Proof Rebuild Impact

For large developments (mathlib-scale):

```bash
# See what would rebuild
lake build --dry-run

# Measure compile times per file
lake build +trace

# Dependency graph
lake graph
```

### Real-World Scale Reference

| Project | Files | Theorems | Build Strategy |
|---------|-------|----------|----------------|
| Mathlib | 4000+ | 100k+ | CI caches, parallel builds |
| CompCert | ~100 | ~1000 | Careful layering |
| This project | ~10 | ~50 | Manual structure |

Mathlib caches at CI level: proven artifacts are shared across builds.

---

*Document created: December 2024*
*Project: lean_experiment - Formally Verified Rust Library*
