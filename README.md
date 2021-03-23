# Coq Formalization

- [coq/](./coq) for Coq formalization
- [spec/](./spec) for Ott specification
- [impl/](./impl) for Haskell implementation (The one discussed in the paper is  [impl/Algo2.hs](./impl/Algo2.hs).


## Building Instructions

Our Coq proofs are verified in **Coq 8.11.2**. We rely on two Coq libraries:
[`metalib`](https://github.com/plclub/metalib) for the locally nameless
representation in our proofs; and
[`LibTactics.v`](http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html),
which is included in the directory.


### Prerequisites

1. Install Coq 8.11.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS. Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. Make sure the version is correct by `git checkout 04b7aeaf82ceb7e00e1e456fc9fea20a85e09f6f`
   5. `make install`

### Build and Compile the Proofs

1. Enter either [coq/](./coq) directory.

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   COQC syntax_ott.v
   ```

4. `syntax_ott.v`, `rules_inf.v` are generated by Ott and LNgen.
Run `make` can reproduce the code (with Ott and LNgen installed).