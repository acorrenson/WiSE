ARG BASE_CONTAINER=coqorg/coq:8.16-ocaml-4.14-flambda
FROM $BASE_CONTAINER
LABEL author="Dominic Steinhoefel"

# Basics
USER coq
COPY --chown=coq:coq . /home/coq/WiSE/
RUN sudo apt-get update
RUN sudo apt-get install -y python2.7 python3-distutils python3-venv

# Install Python 3.10
WORKDIR /tmp
RUN sudo apt-get install -y build-essential zlib1g-dev libncurses5-dev libgdbm-dev libnss3-dev libssl-dev libreadline-dev libffi-dev libsqlite3-dev wget libbz2-dev
RUN wget https://www.python.org/ftp/python/3.10.12/Python-3.10.12.tgz
RUN tar -xvf Python-3.10.12.tgz
WORKDIR /tmp/Python-3.10.12
RUN ./configure
RUN make -j8 build_all
RUN sudo make -j8 altinstall
WORKDIR /tmp
RUN sudo rm -rf /tmp/Python-3.10.12

# Opam dependencies
RUN opam init -y --shell-setup
RUN opam install -y opal z3

# Build WiSE (Coq and OCaml)
WORKDIR /home/coq/WiSE
RUN make

WORKDIR extraction
RUN dune build
WORKDIR ..

# Build PyWiSE
WORKDIR PyWiSE
RUN python3.10 -m venv venv
RUN source venv/bin/activate && pip install -e .[dev,test] && deactivate
WORKDIR ..

CMD ["bash"]
