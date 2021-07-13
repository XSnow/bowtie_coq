# Distributing Intersection and Union Types with Splits and Duality (Artifact)

SplitSubtyping
Xuejing Huang 2021
Distributed under the terms of [the GPL-v3 license](./LICENSE)

- [impl/](./impl) for the Haskell implementation
- [coq/](./coq) for the Coq formalization
- [spec/](./spec) for the Ott specification (that is used to generate the syntax
definition in Coq)

## Haskell Implementation

- Fig. 3 is in [Algo_bcd.hs](./impl/Algo_bcd.hs)
- Fig. 9 and 10 are in [Algo_duo.hs](./impl/Algo_duo.hs)
- [Algo_sub.hs](./impl/Algo_sub.hs) implements the algorithmic subtyping defined
in Fig. 6.
- [Algo_alt.hs](./impl/Algo_alt.hs) implements the algorithmic duotyping in an alternative way (discussed in Section 5.4).

### Building Instructions

1. Install GHCi.
2. Enter [impl/](./impl) directory.
3. Run ghci with the code loaded. There are some example defined in each .hs
that can be used to test.

   ```sh
   ghci Algo2.hs
   *Main> test1
   "(Int -> (Int /\\ Int)) <: (Int -> (Int /\\ Int))  Result: True"
   ```


## Coq Formalization

### Third Party Materials

We use [LibTactics.v](./coq/LibTactics.v) from [the TLC Coq library](https://www.chargueraud.org/softs/tlc/)
by Arthur Chargueraud.

### Building Instructions

Our Coq proofs are verified in the latest version of Coq: **8.13.2**.

#### Prerequisites

1. Install Coq 8.13.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.13.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq).

#### Build and Compile the Proofs

1. Enter [coq/](./coq) directory.

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   COQC Definitions.v
   ```
4. `Definitions.v` is generated by Ott. To reproduce it (some comments will be
lost), please remove it and run `make` (with Ott installed).

### Proof Structure

- [Definitions.v](./coq/Definitions.v) contains all definitions. It is generated
by [spec/rules.ott](spec/rules.ott).

- [TypeSize.v](./coq/TypeSize.v) defines the size of type and proves some
straightforward lemmas in it. It helps us to do induction on the size of type.

- [LibTactics.v](./coq/LibTactics.v) is a Coq library by Arthur Chargueraud.
We downloaded it from [here](http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html).

- [Duotyping.v](./coq/Duotyping.v) is the main file. It contains most theorems
and lemmas in Sec. 4: Lemma 4.1, Theorem 4.5, Theorem 4.6, Lemma 4.7, Lemma 4.8,
Lemma 4.9, Theorem 4.10, and Theorem 4.11.

- [Equivalence.v](./coq/Equivalence.v) relates the two declarative systems and
the two algorithmic systems, respectively.
It contains Theorem 4.2, Lemma 4.3, and Theorem 4.4.

- [Subtyping.v](./coq/Subtyping.v) contains some lemmas about the two subtyping
systems. It is not discussed in the paper. Three of them are used in the
proof of Theorem 4.4 in [Equivalence.v](./coq/Equivalence.v).

- [DistAnd.v](./coq/DistAnd.v) justifies one statement in the paper. It shows
that the rule DS-distAnd (Fig. 4) is omittable.

- [DistSubtyping.v](./coq/DistSubtyping.v) is a stand-alone file which contains
subtyping definitions and related lemmas and theorems.
