# Bayesian Reasoning and Formal Proofs: A Conceptual Exploration

## The Question

Proofs are binary - either proven or not. Bayesian reasoning deals with probabilities and likelihood ratios. Both are strict, precise mathematics. What's the relationship?

- You can write a formal proof for an algorithm that implements Bayes theorem exactly
- But Bayes outputs probabilities, not certainties
- Is there a clean divide between the program and its inputs/outputs?
- Can verification add "quality" to probabilistic outputs?

---

## The Two Domains

```
┌─────────────────────────────────────────────────────────────────┐
│                    FORMAL VERIFICATION                          │
│                    (Binary: ✓ or ✗)                             │
│                                                                 │
│  "This code correctly implements P(A|B) = P(B|A)·P(A)/P(B)"    │
│                                                                 │
│  - Algorithm correctness                                        │
│  - No division by zero                                          │
│  - Probabilities stay in [0,1]                                  │
│  - Numerical stability bounds                                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    BAYESIAN REASONING                           │
│                    (Continuous: 0.0 to 1.0)                     │
│                                                                 │
│  "Given my prior of 0.3 and this evidence, posterior is 0.7"   │
│                                                                 │
│  - Prior beliefs (where do they come from?)                     │
│  - Likelihood estimates (model of the world)                    │
│  - Posterior outputs (only as good as inputs)                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## Different Sources of Uncertainty

| Source | Type | Can we eliminate with proofs? |
|--------|------|------------------------------|
| **Computation bugs** | Epistemic | YES - formal verification |
| **Floating point errors** | Epistemic | Partially - can prove bounds |
| **Wrong priors** | Epistemic | NO - external to formal system |
| **World randomness** | Aleatory | NO - inherent |

### The Shift

Formal verification **shifts** your uncertainty:

```
BEFORE verification:
  "I'm uncertain if my code is right AND uncertain about my priors"

AFTER verification:
  "I'm CERTAIN my code is right, STILL uncertain about my priors"
```

This is valuable! You've eliminated one entire category of doubt.

---

## What You CAN Prove

```lean
-- Bayes theorem itself (from probability axioms)
theorem bayes (P : Event → ℝ) (A B : Event) (hB : P B ≠ 0) :
  P(A | B) = P(B | A) * P(A) / P(B)

-- Your implementation matches the theorem
theorem my_bayes_correct : ∀ prior likelihood evidence,
  my_bayes_impl prior likelihood evidence =
  theoretical_bayes prior likelihood evidence

-- Numerical properties
theorem stays_valid : ∀ inputs, 0 ≤ my_bayes_impl inputs ≤ 1

theorem no_division_by_zero : evidence > 0 → terminates_safely

-- Composition laws
theorem sequential_updates_commute :
  update (update prior e1) e2 = update (update prior e2) e1
```

These are **mathematical truths** about the algorithm itself.

---

## What You CANNOT Prove

```lean
-- This is OUTSIDE the formal system:
theorem my_prior_is_correct :
  my_prior_for_cancer = true_base_rate_of_cancer
  -- ??? How would you even state this formally?
```

The prior is a **belief about the world**, not a mathematical statement. It's like trying to prove "the sky is blue" in a theorem prover - the formal system talks about syntax and computation, not the physical world.

### The Map-Territory Distinction

- **Map**: Your probability model (can be formally verified)
- **Territory**: The actual world (cannot be formally captured)
- **Correspondence**: Whether your model matches reality (empirical, not provable)

---

## Does Verification Add "Quality" to Outputs?

Yes, but in a specific way:

```
Unverified Bayesian engine:
  Input: prior=0.3, LR=1.2
  Output: 0.34 (maybe? could be buggy)
  Confidence: ???

Verified Bayesian engine:
  Input: prior=0.3, LR=1.2
  Output: 0.34 (DEFINITELY the correct computation)
  Confidence: Exactly as good as your inputs
```

The verified version gives you a **clean separation of concerns**:

- If the output is wrong, it's 100% because your inputs were wrong
- You eliminated "maybe there's a bug" from your uncertainty
- You can focus skepticism on priors and model, not implementation

---

## A Practical Analogy

**Verified Bayesian code** is like a **certified accountant**:

| Accountant Guarantees | Accountant Cannot Guarantee |
|-----------------------|-----------------------------|
| Arithmetic is correct | Numbers you provided are accurate |
| Tax rules are followed | Tax code is fair |
| No calculation errors | You won't be audited |
| Proper documentation | Your business is profitable |

Similarly:

| Verified Code Guarantees | Cannot Guarantee |
|--------------------------|------------------|
| Bayes formula applied correctly | Your priors are calibrated |
| No division by zero | Your model matches reality |
| Probabilities in [0,1] | Posterior is "true" |
| Numerical stability | Your likelihood estimates |

---

## The Composition Question

If you have:
- 95% confidence in your priors (calibrated from historical data)
- 100% confidence in computation (formally verified)
- Output: 70% posterior

What's your "total" confidence? This gets philosophically murky:

### 1. Frequentist View
Run the verified code on calibrated priors → outputs should be well-calibrated too. If your priors were right 95% of the time historically, and computation is perfect, outputs should be right ~95% of the time.

### 2. Fully Bayesian View
Put a probability distribution over your priors, propagate through verified computation → get distribution over posteriors. Your uncertainty about priors becomes uncertainty about outputs.

### 3. Pragmatic View
Verified computation is one less thing to worry about. Focus your skepticism on priors and model. The output is "trustworthy given the inputs."

---

## The Venn Diagram

```
    ┌───────────────────────────────────────────────┐
    │          MATHEMATICS                          │
    │  ┌─────────────────────────────────────────┐  │
    │  │      FORMAL PROOFS                      │  │
    │  │  - Probability axioms (Kolmogorov)      │  │
    │  │  - Bayes theorem derivation             │  │
    │  │  - Algorithm correctness                │  │
    │  │  ┌─────────────────────────────────┐    │  │
    │  │  │   VERIFIED CODE                 │    │  │
    │  │  │   (your Bayesian engine)        │    │  │
    │  │  └─────────────────────────────────┘    │  │
    │  └─────────────────────────────────────────┘  │
    │                                               │
    │  ┌─────────────────────────────────────────┐  │
    │  │      PROBABILITY THEORY                 │  │
    │  │  - Distributions                        │  │
    │  │  - Inference rules                      │  │
    │  │  - Decision theory                      │  │
    │  │  - Information theory                   │  │
    │  └─────────────────────────────────────────┘  │
    └───────────────────────────────────────────────┘
                         │
                         │ (interface to reality)
                         ▼
    ┌───────────────────────────────────────────────┐
    │          THE WORLD                            │
    │  - "True" base rates                          │
    │  - Actual causal relationships                │
    │  - Data generating processes                  │
    │  - Physical phenomena                         │
    │                                               │
    │  (Cannot be formally proven, only modeled)    │
    └───────────────────────────────────────────────┘
```

The formal system can reason about **probability as a mathematical object**, but the connection between `P(cancer)` in your model and actual cancer rates is **external** - it's the correspondence between map and territory.

---

## Hierarchy of Certainty

```
Level 5: Axioms of probability (assumed true, foundational)
    │
    ▼
Level 4: Bayes theorem (proven from axioms)
    │
    ▼
Level 3: Your algorithm (proven to implement Bayes)
    │
    ▼
Level 2: Your code (proven to implement algorithm)
    │
    ▼
Level 1: Your priors and likelihoods (beliefs, not provable)
    │
    ▼
Level 0: The actual world (unknowable with certainty)
```

Formal verification gives you certainty at levels 2-4. Levels 0-1 remain uncertain by nature.

---

## Practical Applications

A verified Bayesian inference library would be genuinely useful:

### Medical Diagnosis
- Verified computation of risk scores
- Proven correct combination of multiple test results
- Auditable reasoning chain

### Legal Evidence
- Formally correct likelihood ratio calculations
- Provably sound evidence combination
- No hidden bugs in forensic software

### Scientific Analysis
- Reproducible, provably correct statistics
- Verified MCMC samplers
- Trustworthy uncertainty quantification

### Autonomous Systems
- Verified sensor fusion
- Proven correct belief updates
- Auditable decision making

---

## What Would We Prove?

```lean
-- Core Bayes
theorem bayes_update_correct :
  ∀ prior likelihood,
  bayesian_update prior likelihood = prior * likelihood / evidence

-- Conjugate priors
theorem beta_binomial_conjugate :
  ∀ α β successes failures,
  posterior (Beta α β) (Binomial successes failures) =
  Beta (α + successes) (β + failures)

-- MCMC correctness
theorem metropolis_hastings_detailed_balance :
  ∀ proposal target,
  satisfies_detailed_balance (mh_step proposal target)

-- Numerical bounds
theorem no_catastrophic_cancellation :
  ∀ inputs ∈ valid_range,
  |computed - true| < ε

-- Probability laws
theorem total_probability_one :
  ∀ distribution, sum distribution = 1

theorem non_negative :
  ∀ event, P event ≥ 0
```

---

## The Deep Insight

> **Formal verification eliminates epistemic uncertainty about computation, leaving only epistemic uncertainty about the world and aleatory uncertainty inherent in probability.**

Or more simply:

> **Verified Bayesian code lets you be uncertain about the right things - your beliefs about the world - rather than wasting uncertainty on "did I implement this correctly?"**

This is the same value proposition as all formal verification: not that it makes everything certain, but that it **localizes** uncertainty to where it belongs.

---

## Connection to Other Ideas

### Gödel's Incompleteness
Some truths are outside any formal system. The "true prior" for a real-world phenomenon is analogous - it's a fact about reality that can't be proven within mathematics.

### Halting Problem
We can't always know if a program will halt. Similarly, we can't formally prove that our model of the world is correct - that's an empirical question.

### Type Theory
Types are propositions, programs are proofs. A verified Bayesian program is a proof that "this computation follows from the axioms of probability." But the types can't capture "this prior is correct."

### Philosophy of Science
Popper: theories can be falsified, not proven. Similarly, Bayesian models can be updated with evidence, but never "proven correct" - only "not yet falsified."

---

## Summary

| Question | Answer |
|----------|--------|
| Can you prove Bayes theorem? | Yes, from probability axioms |
| Can you prove code implements Bayes? | Yes, with formal verification |
| Can you prove your priors are correct? | No, that's about the world |
| Does verification help? | Yes, eliminates one source of uncertainty |
| Is there a clean divide? | Yes: computation (provable) vs. beliefs (empirical) |

The formal system and the probabilistic outputs live in **different epistemic categories**:
- **Proofs**: Binary, internal to mathematics
- **Probabilities**: Continuous, interface between math and world
- **Verification**: Proves the bridge is sound, not that it leads where you want
