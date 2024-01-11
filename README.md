# full-iso
Extending iso-recursive type systems (with unfold/folds) to a more generalized form via casting



## Project Structure

Proved sound projects:

- `cast_main`: the main project, containing the STLC + full-iso type system described above 
- `cast_det`: does not define a cast language, the casting relation is a deterministic cast relation. This system is too weak to achieve the goal of this project.
- `cast_rcd`: extend `cast_main` with merges and single field records (but without subtyping)
- `cast_main_sub`: STLC + full-iso type system + iso-recursive subtyping, type safety proved


Ongoing projects:
- `cast_main_ext`: `cast_main` + sequential casts + fixpoint casts



## TODO:

- [x] The type safety for `cast_main_ext`
- [ ] Typing equivalence to the equi-recursive type system
  - [x] If `G |-i E : A` then `G |- e |E| : A`
  - [ ] If `G |- e : A` then exists `E`, `G |-i E : A /\ e = |E|`
- [ ] Behavioral equivalence to the equi-recursive type system
  - [x] If `E -->i E'` then `|E| -->e* |E'|`
  - [ ] If `⋅ |- e : T ▷ E` and ` e -->e  e'` then exists `E'`, `⋅ |- e' : T ▷ E' /\ E -->i* E'`
- [ ] Full-iso causes no computation overhead
  - [ ] If `⋅ |- e : T ▷ E` then `|E| = e` 
- [ ] Check if with Amber rules, the equivalence result can be extended to subtyping




## Related work

- [Abati 1996] Syntactic Considerations on Recursive Types
- [Patrignani 2021] On the Semantic Expressiveness of Recursive Types






## Introduction

In iso-recursive type systems, the type `mu X. T` is isomorphic to `T[X -> mu X. T]`, witnessed by the unfold and fold operators. 

```
e : mu X. T
-------------------- Typing-Unfold
unfold [mu X. T] e : T[X -> mu X. T]


e : T[X -> mu X. T]
-------------------- Typing-Fold
fold [mu X. T] e : mu X. T

---------------------------- Step-UnfoldFold
unfold [mu X. T] (fold [mu X. T] v) --> v
```

However, this isomorphism is not enough to express some interesting programs. Examples can be found in CP languages in which we need to first implement recursive methods on several datatype constructors, and then combine them together to form a recursive datatype. When we combine them together, the fold operation works not on a term of type `T[X -> mu X. T]`, but on a function type from the constructor arguments to `T[X -> mu X. T]`. 

Therefore, it is interesting to explore whether we can extend the iso-recursive type system to a more generalized form, in which the unfold/fold operation can work not only on a recursive type, but also other types that contain recursive type components.

In this project, we propose the following typing rules and develop a type system called `full-iso`:

```
e : A
A ~~> B : c
----------------------- Typing-Cast
e : B
```

In which `A ~~> B : c` means that `A` can be cast to `B` witnessed by a cast language `c`. The cast language `c` describes the cast operations that can be used to cast `A` to `B`. For example,

```
------------------- Cast-id
A ~~> A : id


------------------- Cast-unfold
mu X. T ~~> T[X -> mu X. T] : unfold [mu X. T]


------------------- Cast-fold
T[X -> mu X. T] ~~> mu X. T : fold [mu X. T]


A1 ~~> B1 : c1
A2 ~~> B2 : c2
------------------- Cast-arr
A1 -> A2 ~~> B1 -> B2 : c1 -> c2
```

With the above rules, (plus some other features in CP, such as merges, distributive subtyping, polymorphism, etc), we can encode modular programming features.

Moreover, this work also draws connections between the iso-recursive type system and the equi-recursive type system. Traditionally, transforming equi-recursive typed terms into an iso-recursive type system requires inserting unfold/fold operations. This is typically done by applying a coercion function to the term. However, the application of the coercion on function types will change the computation structure. Therefore it poses challenges to prove that the converted term has the same behavior as the original term, since erasing the unfold/folds in converted term gets a different term from the original equi-recursive typed term. In our work, it is possible to insert direct casts on function types, which will not change the computation structure. Therefore, it can be hoped that the converted term has the same behavior as the original term, with a simpler proof.


## Building Instructions

### Prerequisites

1. Install Coq 8.13.1. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.13.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed, then install `Metalib`:
   1. Open terminal
   2. `git clone -b coq8.10 https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. `make install`

3. Make sure `Haskell` with `stack` is installed, then install `LNgen`:
   1. Open terminal
   2. `git clone https://github.com/plclub/lngen`
   3. `cd lngen`
   4. `stack install`

4. Install `Ott 0.32` if you want to rewrite the rules. Make sure `opam` is installed:
   1. Open terminal
   2. `git clone https://github.com/sweirich/ott`
   3. `cd ott`
   4. `opam pin add ott .`
   5. `opam repo add coq-released https://coq.inria.fr/opam/released`
   6. `opam pin add coq-ott 0.32`

   Check the [Ott website](https://www.cl.cam.ac.uk/~pes20/ott/top2.html#sec7) for detailed instructions. Remember to switch to the correct [forked version](https://github.com/sweirich/ott) of `Ott 0.32` during the installation process.


### Build Each Project

Each project contains a `spec/rules.ott` that specifies the rules of the type system. In `doc` directory there is a PDF version of the rules. The root of each project contains all the Coq proofs.

Some useful `make` commands:
- `make rules` will build the LaTeX rules (`doc/rules.tex`) from `rules.ott`, together with the `syntax_ott.v` file, which contains the Coq definitions of the rules automatically generated by `Ott`
- `make pdf` will build a pdf based on the LaTeX rules and the `main.tex`
- `make` will build all the Coq proofs
