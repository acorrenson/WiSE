ARG BASE_CONTAINER=coqorg/coq:8.16-ocaml-4.14-flambda
FROM $BASE_CONTAINER
LABEL author="Dominic Steinhoefel"

USER coq
COPY --chown=coq:coq . /home/coq/WiSE/
RUN sudo apt-get update
RUN sudo apt-get install -y python2.7 python3-distutils 

RUN opam init -y --shell-setup
RUN opam install -y opal z3
# RUN opam pin -y coq 8.13.2

WORKDIR /home/coq/WiSE
RUN make

WORKDIR extraction
RUN dune build
WORKDIR ..

CMD ["bash"]
