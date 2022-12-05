# A Bowtie for a Beast (Artifact)

## List of claims

The key technical results in this paper have been proven using a
combination of pencil-and-paper proofs and a Coq development. The Coq
development formalizes certain type-level parts of the semantics,
including subtyping, dispatch, and some key properties of disjointness.

- Definitions

    Most of the definitions are formalized in `coq/Definitions.v`, unless
    otherwise specified.
    Since the coq file is generated from `spec/rules.ott`, these definitions can
    also be found in the Ott file, which might be easier to read.

  + Types, negative types, and elimination types defined in Fig. 1 of the paper
    correspond to `typ`, `isNegTyp`, and `Fty`.

    Types constructed by applying `c` to `A` are represented by record types. Record
    labels include left, right, and all natural numbers.

  + Declarative subtyping defined in Fig. 5 of the paper corresponds to
    `declarative_subtyping`.

  + Mergeability and distinguishability defined in Fig. 6 of the paper
    correspond to `Mergeability` (related axioms in `MergeabilityAx`) and
    `Distinguishability_Dec` (related axioms in `DistinguishabilityAx_Dec`).

    For mergeability, we make the symmetric rule implicit in Coq and adding
    three more rules `MergeIntersectSym`, `MergeUnionSym`, and `MergeAxSym`.

    There is an algorithmic formulation of distinguishability which is equivalent
    to the paper definition in Coq:`Distinguishability`.

  + Union splitting, intersection splitting, algorithmic subtyping, and type-level
    dispatch defined in Fig. 8 of the paper correspond to `splu`, `spli`,
    `AlgorithmicSubtyping`, and `ApplyTy`.
    The negation of these three relations are defined as `ordu`, `ordi`, and
    `NApplyTy`.

  + Value types and elimination frame types defined in Fig. 9 of the paper
    corresponds to `isValTyp` and `isValFty`.

- Lemmas and theorems

  + Lemma 4.1 (Soundness and Completeness of Type-level Dispatch) of the paper
    corresponds to the following Coq lemmas in `coq/ApplyTy.v`:
    `applyty_soundness_1`, `applyty_completeness_1_all`,
    `applyty_soundness_2`, and `applyty_completeness_2`.

  + Lemma 5.1 (Soundness and Completeness of Algorithmic Subtyping) of the paper
    corresponds to `Theorem dsub2asub` in `coq/DistSubtyping.v`

  + Lemma 5.2 (Monotonicity of Type-Level Dispatch) of the paper
    corresponds to the following Coq lemmas in `coq/ApplyTy.v`:
    `monotonicity_applyty_1` and `monotonicity_applyty_2_1`.

- Others

  + `Theorem decidability` in `coq/DistSubtyping.v` proves that the algorithmic
    formulation of subtyping is decidable.

  + The negation of union splitting (`splu`) is defined as `ordu`. The
    correctness of the definition is justified by `Lemma ordu_or_split` and
    `Lemma splu_ord_false` in `coq/DistSubtyping.v`. Similarly we have
    `Lemma ordi_or_split` and `Lemma spli_ord_false` for the negation of
    intersection splitting, as well as `Lemma applyty_total` and
    `Lemma applyty_contradication` for the negation of type-level dispatch.

  + The value coverage and elimination coverage relations in the technical
    appendix A are defined as `PositiveSubtyping` and `NegativeSubtyping`
    (the two arguments are swapped) in `coq/Definitions.v`.

  + Similar types in Fig. 11, technical appendix C correspond to
    `Similarity`  in `coq/Definitions.v`.

  + Some lemmas in appendix C are proved in Coq: C.1-C.16, C.25, and C.30-C.32.
    The correspondence is specified in the appendix.

## Download, installation, and sanity-testing

- The stable URL of the artifact (including the virtual machine image) is [HERE](https://zenodo.org/record/7151518).

- The image is also available on the Docker Hub with the name `sxsnow/bowtie`.

- The source code is also available at [GitHub](https://github.com/XSnow/bowtie_coq).

### Use the Docker image

The Docker image includes the code and all dependencies. To use it, you need to have
Docker installed in your machine. Then you can either 1) execute the following two commands
if you have downloaded the offline docker image,

  ```
  xzcat docker_image.tar.xz | docker import - bowtie
  docker run -it --user=coq --workdir=/home/coq bowtie /bin/bash -l
  ```

or 2) get the container from Docker Hub and derive a container from it.

  ```
  docker run -it sxsnow/bowtie
  ```

Now you have run the container, and you can skip the next section.

### Prerequisites for building from scratch

- Coq **8.14.1**. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.14.1).

- [Metalib](https://github.com/plclub/metalib) for the locally nameless
  representation. You can down the code from GitHub and install the library locally.
  We use the latest verison `be0f81c`.

  ```
  git clone https://github.com/plclub/metalib
  cd metalib/Metalib
  git checkout be0f81c
  make install
  ```

  Or use opam to install it:

  ```
  opam update
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam install coq-metalib
  ```

- [LibTactics.v](https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html)
  by Arthur Chargueraud. The file is included in the artifact.

- [Ott 0.31](https://github.com/ott-lang/ott/releases/tag/0.31) and
  [LNgen coq-8.10](https://github.com/plclub/lngen/releases/tag/coq-8.10).

  `Ott` and `LNgen` are used to generate some Coq code from `spec/rules.ott`.
   You can run all code without them installed unless you want to modify the
   Ott definitions and generate the coq files.

   Ott can be installed via opam, just replace the last line in the above commands
   for Metalib by:

  ```
  opam install ott.0.31
  ```

   For LNgen, one option is to use cabal to build and install it:

  ```
  curl -LJO https://github.com/plclub/lngen/archive/refs/tags/coq-8.10.zip
  unzip lngen-coq-8.10.zip
  cd lngen-coq-8.10
  cabal new-build
  cabal new-install
  ```

   Cabal can be installed via [GHCup](https://www.haskell.org/ghcup/). Note that
   you need to adjust your PATH variable (you can follow the interactive instructions).

   You can also use stack to install LNgen(instruction [here](https://github.com/plclub/lngen)).

### Sanity-testing

To compile the proofs:

1. Enter [coq](./coq) directory.

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):

   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   COQC Definitions.v
   ```

## Evaluation instructions

1. Check all the files can be complied.

2. Verify all the listed claims correspond to Coq code faithfully.

3. Find all the occurrences of `admit`, `Admitted`, and `Axiom`. All the proofs
   are complete so no proof uses `admit` or `Admitted`. Two axioms are introduced
   by LibTactics: `Axiom inj_pair2` can be proved with `Eqdep` imported.
   `Axiom skip_axiom : True` has no impact to the proofs as it has
   type `True`.

4. `Definitions.v` is generated by Ott. To reproduce it, please remove it and
    run `make` (with Ott installed).
   `LN_Lemmas.v` (generated by LNgen) can also be reproduced in the same way
    with LNgen installed.

## Additional artifact description

### Proof Structure

- [spec/](./spec) for the Ott specification (that is used to generate the syntax
  definition in Coq)

- [coq/](./coq) for the Coq formalization

  + [Definitions.v](./coq/Definitions.v) contains all definitions used in the coq
    formalization. It is generated from [spec/rules.ott](spec/rules.ott).

  + [LN_Lemmas.v](./coq/LN_Lemmas.v) contains lemmas about locally nameless encoding.
    It is also generated from the Ott file.

  + [LibTactics.v](./coq/LibTactics.v) is a Coq library by Arthur Chargueraud.

  + [DistSubtyping.v](./coq/DistSubtyping.v) contains subtyping-related proofs.

  + [SimpleSub.v](./coq/SimpleSub.v) is about the coverage relations.

  + [ApplyTy.v](./coq/ApplyTy.v) proves the soundness and completeness,
    monotonicity, and some inversion lemmas of the type-level dispatch relation.

  + [Distinguishability.v](./coq./Distinguishability.v) is about the distinguishability
    relation.

  + [Dispatch.v](./coq/Dispatch.v) is about the disptach lemma and inversion lemmas
    on type-level dispatch.
