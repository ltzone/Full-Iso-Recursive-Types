# Full Iso-recursive Types (Artifact)

## Introduction

This folder contains the artifact for OOPSLA'24 paper *Full Iso-recursive Types*. You can open [README_Artifact.pdf](./README_Artifact.pdf) to view the rendered version of the document.

We provide both pre-configured Docker image and original source code in the artifact. You may choose either one to use.

### Proof Assistant and Libraries Dependency

Our proofs are verified in **Coq 8.13.2**. We rely on the Coq library:
[`metalib`](https://github.com/plclub/metalib/releases/tag/coq8.10) to formalize variables and binders using the Locally Nameless representation (Aydemir et al., 2008) in our proofs.
We use [`Ott`](https://github.com/sweirich/ott) to write the definitions and [`LNgen`](https://github.com/plclub/lngen) to generate Locally Nameless definitions and proofs.
We also use [`LibTactics.v`](./cast_main/LibTactics.v) from [the TLC Coq library](https://www.chargueraud.org/softs/tlc/)
by Arthur Chargueraud.

### Proof Structure

There are two directories in this artifact. The `cast_main` directory contains the proofs for the main system presented in Section 3 and Section 4 of the paper. The `cast_sub` directory contains the proofs for the main system extended with subtyping presented in Section 5 of the paper.

The `cast_main` and `cast_sub` share the same structure, in which all the proof files have a sequential dependency, as can be found in `_CoqProject` file of each directory. The proof starts from `syntax_ott.v`, which is generated from the Ott specification in `spec` directory, and ends with `theorems.v`. The `theorems.v` file contains most of the main theorems of the paper. There is also a `doc` directory that contains a latex pdf generated from the Ott specification that presents all the rules of each system.

In addition, within `cast_sub` there is a subdirectory `subtyping` which contains the Coq proofs from the [artifact](https://github.com/juda/Iso-Recursive-Subtyping/tree/master/Journal/src) of the paper "Revisiting Iso-recursive Subtyping" (Zhou et al. 2022). We transported their results (e.g. unfolding lemma) to our setting through `subtyping.v` in the `cast_sub` directory.

#### Key Definitions in the Paper

| Definition | File | Notation in Paper | Name in Coq
| ----- | ------- | ------ | ------
| Fig. 2. Brandt and Henglein's equi-recursive type equality | syntax_ott.v | $H \vdash A \doteq B$ | `eqe2` |
| Fig. 4. Typing                                             | syntax_ott.v | $\Gamma \vdash e: A $ | `Typing` |
| Fig. 4. Type Casting                                       | syntax_ott.v | $\Delta; \mathbb{E} \vdash A \hookrightarrow B : c $ | `TypCast` |
| Fig. 5. Equi-recursive typing with rule Typ-eq             | syntax_ott.v | $\Gamma \vdash_e e : A $ | `EquiTyping` |
| Fig. 5. Full iso-recursive elaboration                     | syntax_ott.v | $\Gamma \vdash_e e : A \rhd e' $ | `EquiTypingC` |
| Fig. 6. Reduction rules                                    | syntax_ott.v | $e \hookrightarrow e' $ | `Reduction` |
| Fig. 7. Iso-recursive Subtyping                            | syntax_ott.v | $\Sigma \vdash A \leq_{i} B $ | `AmberSubtyping` |
| Fig. 7. Equi-recursive Subtyping                           | syntax_ott.v | $\Sigma \vdash A \leq_{e} B $ | `ACSubtyping` |

##### Difference between the Formalization and the Paper

In the formalization of the rules in literature (e.g. Brandt and Henglein's equi-recursive type equality in Fig. 2,
Iso-recursive Subtyping, and Equi-recursive Subtyping in Fig. 7),
we add a type context and well-formedness check to the rules in order to be consistent with the rest of the rules.
The well-formedness conditions are omitted in the paper for simplicity.

#### Paper to Proof Table

- The main system

Contains the proofs for the main system presented in Section 3 and Section 4 of the paper.

The paper to proof table:

| Theorem | File | Name in Coq |
| ------- | ----- | ----------- |
| Theorem 3.1 Soundness of Type Casting                        | theorems.v | `TypCast_soundness` |
| Theorem 3.1 Completeness of Type Casting                     | theorems.v | `TypCast_completeness` |
| Theorem 3.2 Equivalence of Alternative equi-recursive typing | theorems.v | `equi_alt_equiv` |
| Theorem 3.3 Equi-recursive to full iso-recursive typing      | theorems.v | `EquiTypingC_sem` |
| Theorem 3.4 Full iso-recursive to equi-recursive typing      | theorems.v | `typing_i2e` |
| Theorem 3.5 Round-tripping of the encoding                   | theorems.v | `erase_typing` |
| Theorem 3.6 Progress                                         | Progress.v | `progress` |
| Theorem 3.7 Preservation                                     | Preservation.v | `preservation` |
| Theorem 3.8 Full iso-recursive to equi-recursive reduction   | theorems.v | `reductions_i2e` |
| Theorem 3.9 Behavioral equivalence                           | theorems.v | `behavior_equiv` |
 
- The subtyping system

Contains the proofs for the main system extended with subtyping presented in Section 5 of the paper.

The paper to proof table:

| Theorem | File | Name in Coq |
| ------- | ----- | ----------- |
| Theorem 5.1 Reflxixivty of Iso-recursive Subtyping           | subtyping.v | `AmberWFT_refl` |
| Theorem 5.2 Transitivity of Iso-recursive Subtyping          | subtyping.v | `AmberSub_trans` |
| Lemma 5.3 Unfolding Lemma                                    | subtyping.v | `unfolding_lemma` |
| Theorem 5.4(1) Progress                                      | Progress.v | `progress` |
| Theorem 5.4(2) Preservation                                  | Preservation.v | `preservation` |
| Theorem 5.5 Equi-recursive subtyping decomposition           | theorems.v | `subtyping_decomposition` |
| Theorem 5.6(1) Typing Equivalence - soundness                | theorems.v | `typing_i2e` |
| Theorem 5.6(2) Typing Equivalence - completeness             | theorems.v | `EquiTypingC_sem` |
| Theorem 5.6(3) Typing Equivalence - round-tripping           | theorems.v | `erase_typing` |
| Theorem 5.7 Behavioral Equivalence                           | theorems.v | `behavior_equiv` |

## Hardware Dependencies

There is no special requirement on the hardware. Basically a typical laptop can fulfill the resource demand and complete all tasks.
~5GiB disk space is required for loading the Docker image, and the check can be done in a few minutes.

Note that the Docker image is built for x86 architecture, so emulation softwares may be needed if you are working on a platform other than that.

## Getting Started Guide

For reviews who want to the pre-built Docker for quick testing, you can refer to section [Using Docker](#using-docker). Or if you want to create the environ manually, you can refer to section [Manual Installation](#manual-installation).

### Using Docker

Install Docker first. You may refer to the [Docker Docs](https://docs.docker.com/). For Windows users, WSL2 is recommended. Then run the following steps:

1. Start the Docker service on your system;

2. In the artifact directory, run `xz -d fulliso.tar.xz` to decompress the Docker image;

3. Run `docker load -i fulliso.tar` to import the image;

4. Run `docker run -it --rm fulliso` to start the container;

5. You'll see `cast_main` and `cast_sub` directories under the current location; you can `cd` into either one and run `make` to check our proofs.

### Manual Installation

#### Prerequisites

1. Install Coq 8.13.2. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or you could
   download the pre-built packages for Windows and MacOS
   [here](https://github.com/coq/coq/releases/tag/V8.13.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed, then install `Metalib`:
   1. `git clone -b coq8.10 https://github.com/plclub/metalib`
   2. `cd metalib/Metalib`
   3. `make install`

> For checking proofs of the paper, you can stop here and use the provided 
> `syntax_ott.v` and `rules_inf.v` files.
> We have already built these files, which are generated by `LNgen` and `Ott`.
> If you want to modify the rules, you can follow the rest of the instructions
> below to install `LNgen` and `Ott`:

3. Make sure `Haskell` with `stack` is installed, then install `LNgen`:
   1. `git clone https://github.com/plclub/lngen`
   2. `cd lngen`
   3. `stack install`

4. Install `Ott 0.32` if you want to rewrite the rules. Make sure `opam` is installed:
   1. `git clone https://github.com/sweirich/ott -b ln-close`
   2. `cd ott`
   3. `opam pin add ott .`
   4. `opam pin add coq-ott .`

   Check the [Ott website](https://www.cl.cam.ac.uk/~pes20/ott/top2.html#sec7) for detailed instructions. Remember to switch to the correct [forked version](https://github.com/sweirich/ott) of `Ott 0.32` during the installation process.

You may also take the provided [Dockerfile](./Dockerfile) for reference. The Docker image can be built by `docker build -t fulliso .`.

#### Build and Compile the Proofs

1. Enter the coq directory you would like to build.

2. Type `make` in the terminal to build and compile the proofs.

### Expected Output

- For `cast_main`:

```bash
/home/fulliso/cast_main$ make
coqdep -f _CoqProject > .depend
coq_makefile -arg '-w none' -f _CoqProject -o CoqSrc.mk
make[1]: Entering directory '/home/fulliso/cast_main'
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC progress.v
COQC erasure.v
COQC equiRec.v
COQC preservation.v
COQC equiAux.v
COQC theorems.v
make[1]: Leaving directory '/home/fulliso/cast_main'
```

- For `cast_sub`:

```bash
/home/fulliso/cast_sub$ make
coqdep -f _CoqProject > .depend
coq_makefile -arg '-w none' -f _CoqProject -o CoqSrc.mk
make[1]: Entering directory '/home/fulliso/cast_sub'
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC subtyping/Rules.v
COQC subtyping/Infra.v
COQC subtyping/FiniteUnfolding.v
COQC subtyping/Typesafety.v
COQC subtyping/DoubleUnfolding.v
COQC subtyping/AmberBase.v
COQC subtyping/AmberLocal.v
COQC subtyping/AmberSoundness.v
COQC subtyping/PositiveBase.v
COQC subtyping/PositiveSubtyping.v
COQC subtyping/AmberCompleteness.v
COQC subtyping/NominalUnfolding.v
COQC subtyping/AnchorUnfolding.v
COQC subtyping/Decidability.v
COQC subtyping.v
COQC progress.v
COQC erasure.v
COQC equiRec.v
COQC preservation.v
COQC equiAux.v
COQC theorems.v
make[1]: Leaving directory '/home/fulliso/cast_sub'
```

The build should run to the end without any error message produced.

## Step by Step Instructions

### Evaluate the Result

All the claims made by the paper, as shown in section [Proof Structure](#proof-structure), is substantiated by the successful build.

### Check Axioms and Assumptions

To verify the axioms that out proofs rely on, append `Print Assumptions behavior_equiv.` to the end of `theorems.v` (you may need to `sudo apt update && sudo apt install nano -y` (or `vim` based on your preference) first if you are inside the Docker image) and re-run `make`. You will see:

```coq
COQC theorems.v
Axioms:
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
```

It should be the only axiom we rely on, which introduced by the use of `dependent induction`.

### Check Unproved Hypotheses

Run `grep -r "Admitted\." .` under `/home/fulliso`, and you will only see

```
./cast_sub/subtyping.v:Admitted. *)
```

which is inside the comment, meaning our proofs do not contain any unproved hypotheses.

### Other `make` Commands

```bash
make rules # Generate the syntax_ott.v and rules_inf.v files
make pdf   # Generate the latex pdf from the Ott specification
make clean # Clean all the files generated by Coq checking
make realclean # Clean all the generated files including documents
```

You may make use of these commands after modifying the rules or proofs.

Note that the `make pdf` command requires a $\LaTeX$ installation. If you are using Docker, you may `docker cp` the `doc` folders out of the container after `make rules`, and run `latexmk -pdf main.tex` to generate the PDF file. Also note that `make pdf` will call <code>latexmk<strong>.exe</strong></code> under WSL. If that's not your case (i.e. the $\LaTeX$ is directly installed inside the WSL), you may modify the `Makefile` by changing the `LATEXMK` variable.

## Reusability Guide

The core pieces of the artifact intended to be reused is the rules, theorems, and the proofs. Future users can refer to the [Proof Structure](#proof-structure) section for grasping the existing proofs, and make their own modification based on the existing ones.
They may use the convenient shortcuts provided such as `make pdf` to generate the documentation, which facilitates the reusability.

The proofs may need to be adjusted if the downstream user is using a differenct Coq version, which can be a limitation in the reusability of this artifact.