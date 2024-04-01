
## Key Definitions in the Paper

| Definition | File | Notation in Paper | Name in Coq
| ----- | ------- | ------ | ------
| Fig. 2. Brandt and Henglein's equi-recursive type equality | syntax_ott.v | $H \vdash A \doteq B$ | `eqe2` |
| Fig. 4. Typing                                             | syntax_ott.v | $\Gamma \vdash e: A $ | `Typing` |
| Fig. 4. Type Casting                                       | syntax_ott.v | $\Delta; \mathbb{E} \vdash A \hookrightarrow B : c $ | `TypCast` |
| Fig. 5. Equi-recursive typing with rule Typ-eq             | syntax_ott.v | $\Gamma \vdash_e e : A $ | `EquiTyping` |
| Fig. 5. Full iso-recursive elaboration                     | syntax_ott.v | $\Gamma \vdash_e e : A \rhd e' $ | `EquiTypingC` |
| Fig. 6. Reduction rules                                    | syntax_ott.v | $e \hookrightarrow e' $ | `Red` |

Note, in the formalization of Brandt and Henglein's type equality, unlike the paper,
  we add a type context and well-formedness check to the rules, to be consistent with the rest of the rules.


## Paper to Proof Table

Contains the proofs for the main system presented in Section 3 and Section 4 of the paper.

The paper to proof table:

| Theorem | File | Name in Coq |
| ------- | ----- | ----------- |
| Theorem 3.1 Determinism of type casting                      | TBD | TBD |
| Theorem 3.2 Soundness of Type Casting                        | theorems.v | `TypCast_soundness` |
| Theorem 3.2 Completeness of Type Casting                     | theorems.v | `TypCast_completeness` |
| Theorem 3.3 Equivalence of Alternative equi-recursive typing | theorems.v | `equi_alt_equiv` |
| Theorem 3.4 Equi-recursive to full iso-recursive typing      | theorems.v | `EquiTypingC_sem` |
| Theorem 3.5 Full iso-recursive to equi-recursive typing      | theorems.v | `typing_i2e` |
| Theorem 3.6 Round-tripping of the encoding                   | theorems.v | `erase_typing` |
| Theorem 3.7 Progress                                         | Progress.v | `progress` |
| Theorem 3.8 Preservation                                     | Preservation.v | `preservation` |
| Theorem 3.9 Full iso-recursive to equi-recursive reduction   | theorems.v | `reductions_i2e` |
| Theorem 3.10 Behavioral equivalence                          | theorems.v | `behavior_equiv` |
