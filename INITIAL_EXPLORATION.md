# Initial Exploration: Verified Rust with Lean

## Project Goal

Build a formally verified string theory toolkit in Rust, with mathematical proofs in Lean 4 via the Aeneas toolchain. Use this for a genetic algorithm evaluating Calabi-Yau threefolds.

## What We Built

```
lean_experiment/
├── rust/src/
│   ├── math.rs         # gcd, pow, factorial, is_prime (18 tests)
│   ├── strings.rs      # validate_and_process, is_palindrome
│   └── fibonacci.rs    # iterative, matrix, bounded implementations
├── LeanExperiment/
│   ├── Example1_Arithmetic.lean    # 1 + 1 = 2 proven
│   ├── Example2_Strings.lean       # String proofs
│   ├── Example3_Monads.lean        # Option monad laws
│   ├── Example4_IO.lean            # IO effects
│   ├── Example5_Validation.lean    # Input validation with proofs
│   ├── CategoryTheory.lean         # Tests vs proofs
│   └── SecurityDuality.lean        # Pentesting as inverted testing
└── README.md
```

## The Verification Workflow

```
Rust Code → Charon (MIR extraction) → LLBC → Aeneas → Pure Lean → Proofs
```

Commands:
```bash
cd rust
nix run github:aeneasverif/aeneas#charon                    # Extract Rust → LLBC
nix run github:aeneasverif/aeneas -- -backend lean *.llbc   # LLBC → Lean
```

---

## Key Insight #1: Tests vs Proofs

### What is a Unit Test?

A test is a **point sample** from a function's graph:

```
Test:  f(3) = 6              ← ONE input-output pair
Proof: ∀n. f(n) = 2*n        ← ALL input-output pairs
```

The test is looking through a keyhole. The proof is having the blueprint.

### The "Bit" of a Test

A test reduces a function to a boolean:

```
UnitTest : (f : A → B) × (x : A) × (y : B) → Bool
         = "does f(x) equal y?"
```

This boolean is the **shadow** of a proof projected onto `{0, 1}`. It answers "yes/no" but loses the **structure** of WHY.

```lean
-- The test: just true/false
#eval double 3 == 6        -- true : Bool (no information about WHY)

-- The proof: a witnessing term
#check (rfl : double 3 = 6)  -- a TERM that proves the equality
```

### Curry-Howard Correspondence

```
Types    ↔  Propositions
Programs ↔  Proofs
```

- A test **evaluates** to true/false
- A proof **constructs** a witness term

### The Hierarchy

| Level | Method | Coverage |
|-------|--------|----------|
| 0 | No tests | "Trust me bro" |
| 1 | Unit tests | Point samples |
| 2 | Property tests | Random samples |
| 3 | Symbolic execution | All paths |
| 4 | **Formal proof** | **ALL inputs** |

**One proof replaces infinitely many tests.**

---

## Key Insight #2: Pentesting is Inverted Property Testing

### The Duality

```
Property Test:  "For random x, does P(x) hold?"      → Confirm universal
Pentest:        "For adversarial x, does ¬P(x)?"     → Refute universal
```

Both are **existential searches** in input space:

| Approach | Searching for | Success means |
|----------|---------------|---------------|
| Property test | Confirmation | No counterexample found |
| Pentest | Violation | Counterexample (exploit) found |
| Formal proof | — | Search space is **CLOSED** |

### The Logical Structure

```
Defender claims:  ∀x. Safe(x)     "All inputs are safe"
Attacker seeks:   ∃x. ¬Safe(x)    "Some input is unsafe"
```

These are **negations** of each other:

```
¬(∀x. P(x))  ↔  ∃x. ¬P(x)
```

The pentester tries to constructively **disprove** the defender's universal claim.

### The Asymmetry of Evidence

| Result | Evidence | Strength |
|--------|----------|----------|
| Test passes | "No counterexample found" | Weak (infinite space remains) |
| Pentest succeeds | "Here is counterexample X" | **Constructive disproof** |
| Formal proof | "No counterexample exists" | **Absolute certainty** |

### A Successful Pentest IS a Proof

```lean
structure Vulnerability (P : α → Prop) where
  exploit : α           -- The malicious input
  breaks : ¬P exploit   -- Proof that it violates the property
```

Finding an exploit **proves** the system is insecure.

### The Shield

If you formally prove `∀x. Safe(x)`:
- The pentester's search space becomes **empty**
- Not "we haven't found an exploit"
- But "**no exploit CAN exist**"

---

## Key Insight #3: Category Theory Perspective

In category theory:
- **Objects** are types
- **Morphisms** are functions
- **Functors** map categories preserving structure

A functor F must satisfy:
```
F(id)    = id           -- Preserve identity
F(g ∘ f) = F(g) ∘ F(f)  -- Preserve composition
```

| Approach | What it checks |
|----------|----------------|
| Test | Specific morphism compositions |
| Proof | ALL morphism compositions |

Once you prove a functor is well-defined, you get infinitely many specific equalities for free.

---

## The AI Opportunity

### Specification Mining

Given tests `{f(0)=0, f(1)=2, f(2)=4, f(3)=6}`:

1. AI **conjectures**: "Maybe `∀n. f(n) = 2n`?"
2. AI **attempts proof** in Lean
3. If succeeds: One theorem replaces infinite tests
4. If fails: Learn counterexample, refine conjecture

### The Race

- AI makes **pentesting** more powerful (finds more bugs faster)
- AI makes **proving** more accessible (fixes bugs permanently)

Eventually: AI proves properties faster than it can find exploits
→ Shift from reactive security to **proactive verification**

---

## For the String Theory Toolkit

### The Goal

| Approach | Confidence Level |
|----------|-----------------|
| "We tested 10,000 CY evaluations" | Could still have bugs |
| "We proved the algorithm preserves CY invariants" | **Mathematically impossible** to be wrong |

### What to Prove

1. **Fitness function** respects Calabi-Yau mathematical structure
2. **Mutation operators** preserve valid CY properties
3. **Selection** doesn't introduce mathematical errors
4. **Convergence** properties of the genetic algorithm

### The Value

A formally verified string theory toolkit would be unprecedented. If professional string theorists use verified code with Lean proofs, the mathematical guarantees transfer to their results.

That's how you get a footnote in a Nobel Prize paper.

---

## Tools Installed

- **Lean 4.25.2** - Theorem prover / programming language
- **Lake** - Lean build system
- **Rust + Cargo** - Systems programming
- **Nix** - Package manager for reproducible builds
- **Charon** - Extracts Rust MIR to LLBC
- **Aeneas** - Translates LLBC to pure Lean

## Next Steps

1. Complete Charon/Aeneas extraction of Rust examples
2. Write actual proofs about the generated Lean code
3. Add Mathlib for full category theory support
4. Design the Calabi-Yau data structures in Rust
5. Prove invariant preservation for CY operations

---

## Philosophical Summary

> **A test samples the input space. A proof closes it.**
>
> **A pentest seeks to open what the defender claims is closed.**
>
> **A formal proof makes the search space truly empty—not just unexplored, but nonexistent.**

The bit of a test is ephemeral. The type of a proof is eternal.
