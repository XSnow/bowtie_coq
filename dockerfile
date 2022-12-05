FROM coqorg/coq:8.14.1

# install metalib and ott from opam
# install cabal from ghcup
# install lngen by cabal

RUN sudo apt update && sudo apt install -y vim \
 && opam update -y                                                     \
 && opam repo -y add coq-extra-dev https://coq.inria.fr/opam/extra-dev \
 && opam install -y coq-metalib ott.0.31 \
 && curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh \
 && echo "source /home/coq/.ghcup/env" >> /home/coq/.bashrc \
 && curl -LJO https://github.com/plclub/lngen/archive/refs/tags/coq-8.10.zip \
 && unzip lngen-coq-8.10.zip \
 && source /home/coq/.ghcup/env \
 && ( cd lngen-coq-8.10 && cabal new-build && cabal new-install ; ) \
 && rm -rf lngen-coq-8.10 lngen-coq-8.10.zip

RUN git clone https://github.com/XSnow/bowtie_coq.git
