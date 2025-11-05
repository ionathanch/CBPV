# Call-by-Push-Value

This is a proof development on the metatheory of call-by-push-value,
which makes heavy use of mutual induction,
since the syntax of terms is mutually defined.

```
A ::= Unit | A + A | A × A | U B
B ::= A → B | B & B | F A

v ::= x | () | inl v | inr v | (v, v) | {v}
m ::= v! | λx. m | m v | return v | let x ← m in m
  | case v of {inl x => m; inr x => m}
  | let (x, y) = v in m
  | ⟨m, m⟩ | m.1 | m.2
```

This means that everything from reduction to typing to the logical relation
are all mutually defined, and eliminating them generally requires mutual induction.

## Development structure and dependency graph

The structure of the proofs begins with the usual basics.

* RTC.lean: Reflexive, transitive closure of binary relations
* Syntax.lean: Syntax, renaming, substitution, and contexts
* Typing.lean: Typing rules, renaming, and weakening
* Evaluation.lean: Evaluation of (closed) commands,
  which doesn't evaluate under binders and branches
* CK.lean: CK machine semantics, with soundness and completeness
  with respect to evaluation
* Reduction.lean: Small-step reduction semantics for values and commands,
  which reduces everywhere to normal form

The primary goal of the development is to prove strong normalization:
all reduction paths are normalizing.

* NormalInd.lean: An inductive characterization of strongly normal and neutral terms,
  as well as a notion of strong reduction.
* NormalAcc.lean: The traditional definition of strong normalization
  as an accessibility predicate with respect to reduction.
* OpenSemantics.lean: A logical relation between types and sets of terms
  that are backwards closed with respect to strong reduction.
* Soundness.lean: Semantic typing, defined in terms of the logical relation,
  and the fundamental theorem that syntactic typing implies semantic typing.
* Normalization.lean: Syntactic typing implies semantic typing
  implies strong normalization (inductive)
  implies strong normalization (traditional).

Remaining proof files show interesting properties of CBPV.

* LeftmostOutermost.lean: A deterministic single-step reduction semantics
  based on strong reduction, proven to step to normal forms.
* ClosedSemantics.lean: A logical relations proof that closed, well-typed terms
  are strongly normalizing with respect to evaluation.
* Equivalence.lean: A logical equivalence between closed terms of a type
  with respect to evaluation (subsumes the unary logical relation).
* CBV.lean, CBN.lean: Translations from STLC with fine-grained CBV and CBN semantics,
  along with proofs that they preserve well-typedness and CK machine semantics.
* Antisubstitution.lean (fails checking): An unused substitution lemma,
  similar to the antirenaming lemma.

```
        ╭──────────RTC──────┬─────────╮
        ├───────┬──Syntax───┼─────────┤
        │       │           │         │
        ╽       ╽           ╽         ╽
Evaluation    Typing    NormalInd    Reduction
  │   │       │ │  │        │  │         │    
  │   ╽       ╽ │  │        ╽  ╰─────────│────╼ LeftmostOutermost
  │   CK ─╼ CBV │  │  OpenSemantics      │      Antisubstitution
  │         CBN │  │    │                │
  ╽             ╽  ╽    ╽                ╽
  ClosedSemantics  Soundness         NormalAcc
  Equivalence             │           │
                          ╽           ╽
                          Normalization
```

## When to `@[simp]` and `@[reducible]`

Not all definitions are added to the default `simp` set.
As a general rule, a definition should be added if it is not a type-level term
and:

* It matches on an argument; or
* It does not match on an argument, but is not used in other definitions.

For instance, `Syntax.cons` matches on naturals,
and we want it to be in the simp set so that it reduces on constructors.
However, `Syntax.lift` doesn't match on an argument and is used in `Syntax.renameCom`,
so we don't want it to be in the simp set,
since it will always reduce too far when simplifying `renameCom`,
and prevent theorems about `renameCom` and `lift` from applying.
As another example, `ClosedSemantics.semCtxt` is used within `ClosedSemantics.semCom`,
so it shouldn't be in the simp set, but `semCom` itself can be.

Type-level definitions, especially recursive ones,
often represent predicates that could otherwise be encoded as inductives.
`ClosedSemantics.𝒱` and `ClosedSemantics.𝒞` are such definitions,
in contrast with the inductives `OpenSemantics.𝒱` and `OpenSemantics.𝒞`.
The definitions should be explicitly unfolded as needed,
corresponding with invoking `cases` on the corresponding inductives.
Otherwise, simplification may again reduce too far
and prevent theorems from applying.

Type-level definitions which are just type aliases
should be marked as `@[reducible]` so that instances for typeclasses
on the aliased types can be used.
In particular, definitions consisting of applications of `RTC.RTC`
need to be `@[reducible]` so that `calc` can find the `Trans` instances.
