
## Key Definitions in the Paper

| Definition | File | Notation in Paper | Name in Coq
| ----- | ------- | ------ | ------
| Fig. 2. Brandt and Henglein's equi-recursive type equality | syntax_ott.v | $H \vdash A \doteq B$ | `eqe2` |
| Fig. 4. Typing                                             | syntax_ott.v | $\Gamma \vdash e: A $ | `Typing` |
| Fig. 4. Type Casting                                       | syntax_ott.v | $\Delta; \mathbb{E} \vdash A \hookrightarrow B : c $ | `TypCast` |
| Fig. 5. Equi-recursive typing with rule Typ-eq             | syntax_ott.v | $\Gamma \vdash_e e : A $ | `EquiTyping` |
| Fig. 5. Full iso-recursive elaboration                     | syntax_ott.v | $\Gamma \vdash_e e : A \rhd e' $ | `EquiTypingC` |
| Fig. 6. Reduction rules                                    | syntax_ott.v | $e \hookrightarrow e' $ | `Red` |

Note, the elaboration rule `ETyp-sub` presented in the paper is a lemma instead of a rule in the Coq formalization,
  which can be derived from `ETyp-isub` and `ETyp-eq`.

## Paper to Proof Table

Contains the proofs for the main system presented in Section 3 and Section 4 of the paper.

The paper to proof table:

| Theorem | File | Name in Coq |
| ------- | ----- | ----------- |
| Theorem 5.1 Transitivity of Iso-recursive Subtyping          | subtyping.v | `AmberSub_trans` |
| Theorem 5.2 Unfolding Lemma                                  | subtyping.v | `unfolding_lemma` |
| Theorem 5.3(1) Progress                                      | Progress.v | `progress` |
| Theorem 5.3(2) Preservation                                  | Preservation.v | `preservation` |
| Theorem 5.4 Equi-recursive subtyping decomposition           | theorems.v | `subtyping_decomposition` |
| Theorem 5.5(1) Typing Equivalence - soundness                | theorems.v | `typing_i2e` |
| Theorem 5.5(2) Typing Equivalence - completeness             | theorems.v | `EquiTypingC_sem` |
| Theorem 5.5(3) Typing Equivalence - round-tripping           | theorems.v | `erase_typing` |
| Theorem 5.6(1) Behavioral Equivalence                        | theorems.v | `behavior_equiv` |
