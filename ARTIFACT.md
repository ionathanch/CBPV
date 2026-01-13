# Artifact for _Commuting Conversions and Join Points for Call-By-Push-Value_

This development depends on the [`MutualInduction`](https://github.com/ionathanch/MutualInduction) project,
which contains a tactic for mutual induction, and a macro for join theorems.
These are only meta-level tools for ease of proof development, and contain no proofs themselves.
No other axioms are used other than the
[standard axioms](https://lean-lang.org/doc/reference/4.26.0/Axioms/#standard-axioms)
included in Lean 4:

* `propext` is used pervasively by the `simp` tactic;
* `Quot.sound` is used by `funext`, which in turn is used for well-founded recursion.
  In this development, well-founded recursion is used when mutually defining
  `𝒱`, `𝒞`, and `ℰ` in Equivalence.lean.

Axioms can be checked by adding `#print axioms retGround` to the end of Soundness.lean and rebuilding,
which prints the axioms used by all proofs up to and including `retGround`,
the ultimate theorem of the paper.

While the paper presents the syntax in nominal form,
the development uses de Bruijn indexing for both term and jump variables.
Therefore, there are many omitted proofs dealing with
renaming, substitution, and weakening.
Note that term variables are not intrinsically scoped (Nat),
while the jump variables are (Fin δ).

## Installation and Running

1. Install Lean 4 following the [installation guide](https://lean-lang.org/install/manual/).
2. In the root directory (containing `lakefile.lean`), run `lake build`.
   This will download and install the correct Lean version (v4.26.0).
3. Run `lake build` to typecheck all files in the CBPV directory.

## Development Structure

The structure of the proofs in the CBPV directory begins with the usual basics.

* RTC.lean: Reflexive, transitive closure of binary relations.
* Syntax.lean: Syntax, renaming, substitution, and contexts.
* Typing.lean: Typing rules, renaming, and weakening.
* Evaluation.lean: Small-step evaluation of (closed) computations,
  which doesn't evaluate under binders and branches.

Showing that commuting conversions are valid is done
through a logical equivalence.

* Rejoin.lean: A proof widget for closing over jump contexts.
* Equivalence.lean: The logical equivalence defined over CBPV types,
  and the semantic equivalence closing over value and jump contexts.
* Commutation.lean: Well-typed commutations are semantically equivalent.

Commuting conversions are incorporated into the single-pass transformation,
CC-normalization, which produces CC-normal forms.

* CCNF.lean: CC-normalization and showing that it produces CCNF and preserves typing.
* Soundness.lean: Semantic equivalence of continuations,
  and showing that plugging a term into a continuation
  is semantically equivalent to translating it with an equivalent continuation.

The dependency graph of these proofs is illustrated below.

```
    RTC          Syntax
     ┢────────────╯ ╽
 Evaluation    ╭╴Typing
     ╽   │     │    │
  Rejoin ╰─────│────┤
     ╽         │    ╽
Equivalence ╾──╯  CCNF
     ╽              ╽
Commutation ──╼ Soundness
```

## Definition and Theorem Correspondence

Every definition and theorem (lemma, corollary) in the paper lists
the corresponding proof file and definition or theorem name in the development.
They are collected here for convenience, grouped by proof file.

### Syntax.lean

| Name     | Paper    | Description                 | Notation       |
| -------- | -------- | --------------------------- | -------------- |
| ValType  | Fig. 4   | value types                 | A              |
| ComType  | Fig. 4   | computation types           | B              |
| Val      | Fig. 4   | values                      | v, w           |
| Com      | Fig. 4   | computations                | m, n           |
| cons     | Sec. 5.1 | substitution maps           | σ, τ           |
| substVal | Sec. 3   | substitution (values)       | v{x ↦ w}, v{σ} |
| substCom | Sec. 3   | substitution (computations) | m{x ↦ w}, m{σ} |
| Ctxt     | Sec. 3.2 | typing contexts             | Γ              |
| Dtxt     | Sec. 3.2 | jump contexts               | Δ              |
| Ctxt.In  | Fig. 6   | typing context membership   | x : A ∈ Γ      |
| Dtxt.In  | Fig. 6   | jump context membership     | j : A ↗ B ∈ Δ  |

### Evaluation.lean

| Name        | Paper    | Description                  | Notation |
| ----------- | -------- | ---------------------------- | -------- |
| Eval        | Fig. 5   | single-step evaluation       | m ⇝ m    |
| Evals       | Sec. 3.1 | multi-step evaluation        | m ⇝* m   |
| nf          | Fig. 5   | terminal computations        | tm       |
| det         | Lem. 3.1 | determinism of evaluation    |          |
| Norm        | Def. 3.2 | normalization                | m ⇓ tm   |
| Norm.join   | Cor. 3.2 | determinism of normalization |          |
| Evals.merge | Cor. 3.4 | merging                      |          |

### Typing.lean

| Name        | Paper    | Description                            | Notation      |
| ----------- | -------- | -------------------------------------- | ------------- |
| ValWt       | Fig. 6   | value typing                           | Γ ⊢ v : A     |
| ComWt       | Fig. 6   | computation typing                     | Γ ∣ Δ ⊢ m : B |
| wtWeakenVal | Lem. 3.5 | value weakening (value contexts)       |               |
| wtWeakenCom | Lem. 3.5 | computation weakening (value contexts) |               |
| wtWeakenJ   | Lem. 3.6 | computation weakening (join contexts)  |               |

### Rejoin.lean

| Name        | Paper    | Description | Notation     |
| ----------- | -------- | ----------- | ------------ |
| J           | Sec. 5.1 | join stacks | φ, ψ         |
| Com.rejoin  | Sec. 5.1 | join points | joins φ in m |

### CCNF.lean

| Name         | Paper     | Description                               | Notation          |
| ------------ | --------- | ----------------------------------------- | ----------------- |
| isVal        | Fig. 7    | CCNF values                               | v                 |
| isCom        | Fig. 7    | CCNF tail-free computations               | n                 |
| isCfg        | Fig. 7    | CCNF configurations                       | m                 |
| K            | Sec. 4    | continuations                             | K, k              |
| plug         | Fig. 8    | plugging continuations                    | K[n]              |
| CCval        | Fig. 9    | value CC-normalization                    | ⟦v⟧               |
| CCcom        | Fig. 9    | computation CC-normalization              | ⟦m⟧K              |
| K.jumpify    | Fig. 10   | case expression CC-normalization decision |                   |
| isK.plug     | Lem. 4.1  | plugging preserves CCNF                   |                   |
| Evals.plug   | Lem. 5.12 | plugging preserves reduction              |                   |
| substPlug    | Lem. 5.14 | substitution commutes with plugging       |                   |
| isCCNF       | Lem. 4.2  | CCNF preservation                         |                   |
| wtK          | Fig. 11   | continuation typing                       | Γ ∣ Δ ⊢ K : B ⇒ B |
| wtK.plug     | Lem. 4.3  | plugging preserves typing                 |                   |
| wtK.jumpify  | Lem. 4.4  | let continuation inversion                |                   |
| preservation | Lem. 4.5  | type preservation                         |                   |

### Equivalence.lean

| Name                         | Paper     | Description                            | Notation          |
| ---------------------------- | --------- | -------------------------------------- | ----------------- |
| 𝒱                            | Fig. 12   | value logical equivalence              | (v, w) ∈ ⟦A⟧      |
| 𝒞                            | Fig. 12   | terminal logical equivalence           | (m, n) ∈ ⟦B⟧      |
| ℰ                            | Fig. 12   | computation logical equivalence        | (m, n) ∈ ⟦B⟧*     |
| bwds                         | Lem. 5.2  | backward closure                       |                   |
| bwdsRejoin                   | Lem. 5.3  | backward closure under join points     |                   |
| 𝒱.sym, 𝒞.sym, ℰ.sym          | Lem. 5.4  | symmetry (logical equivalence)         |                   |
| 𝒱.trans, 𝒞.trans, ℰ.trans    | Lem. 5.4  | transitivity (logical equivalence)     |                   |
| semCtxt                      | Fig. 13   | substitution map equivalence           | (σ, τ) ∈ ⟦Γ⟧      |
| semDtxt                      | Fig. 13   | join stack equivalence                 | (φ, ψ) ∈ ⟦Δ⟧      |
| semCtxt.sym, semDtxt.sym     | Lem. 5.5  | symmetry (subst./join equivalence)     |                   |
| semCtxt.trans, semDtxt.trans | Lem. 5.5  | transitivity (subst./join equivalence) |                   |
| semVal                       | Def. 5.6  | value semantic equivalence             | Γ ⊧ v ~ w : A     |
| semCom                       | Def. 5.7  | computation semantic equivalence       | Γ ∣ Δ ⊧ m ~ n : B |
| semVal.sym, semCom.sym       | Lem. 5.8  | symmetry (semantic equivalence)        |                   |
| semVal.trans, semCom.trans   | Lem. 5.8  | transitivity (semantic equivalence)    |                   |
| soundness                    | Thm. 5.9  | fundamental thm. of semantic equiv.    |                   |
| safety                       | Cor. 5.10 | normalization of closed computations   |                   |

### Commutation.lean

The following derived rules are listed in Figures 14 and 15.

| Lean name | Rule name |
| --------- | --------- |
| letLet    | let-let   |
| appLet    | let-app   |
| fstLet    | let-fst   |
| sndLet    | let-snd   |
| letCase   | case-let  |
| appCase   | case-app  |
| fstCase   | case-fst  |
| sndCase   | case-snd  |
| joinJoin  | join-join |

The Lean theorem `caseCase` corresponds to Lemma 6.1 (case-of-case).

### Soundness.lean

| Name        | Paper     | Description                                       | Notation              |
| ----------- | --------- | ------------------------------------------------- | --------------------- |
| semK        | Def. 5.11 | continuation semantic equivalence                 | Γ ∣ Δ ⊧ K ~ K : B ⇒ B |
| soundK      | Thm. 5.13 | fundamental thm. of continuation semantic equiv.  |                       |
| semK.plug   | Lem. 5.15 | equivalence of plugging equivalent continuations  |                       |
| semPlug     | Cor. 5.16 | equivalence of plugging the same continuation     |                       |
| semKletin   | Lem. 5.17 | semantic equivalence of plugging let expressions  |                       |
| semKcase    | Lem. 5.18 | semantic equivalence of plugging case expressions |                       |
| semKjoin    | Lem. 5.19 | jump equivalence of plugging                      |                       |
| soundCCjoin | Lem. 5.20 | jump equivalence of CC-normalization              |                       |
| soundCC     | Thm. 5.21 | equivalence of plugging and CC-normalization      |                       |
| soundCCnil  | Cor. 5.22 | equivalence of CC-normalization                   |                       |
| isGround    | Sec. 5    | ground value types                                | T                     |
| 𝒱.ground    | Lem. 5.23 | equivalent ground values are equal                |                       |
| retGround   | Thm. 5.24 | CC-normalization preserves ground returners       |                       |
