# WiSE

**WiSE** (**W**hat **i**s **S**ymbolic **E**xecution) is a formally (mechanically) verified symbolic execution-based bug-finder for imperative programs.
The motivation and underlying principles of WiSE are presented in our paper "Engineering a Formally Verified Automated Bug Finder" ([Preprint on ArXiv](https://arxiv.org/abs/2305.05570)).

This repository provides

- Our implementations and correctness proofs in Coq (directory `Coq/`);
- The OCaml harness and instructions for deriving the OCaml version of WiSE (directory `Coq/extraction/`);
- The Python derivative PyWiSE (directory `PyWiSE/`).

## Running the Examples from the Paper

The Coq version of WiSE was mechanically verified.
To demonstrate that we developed working tools, we evaluated WiSE with three example programs:
The computation of a number’s factorial and integer square root and the greatest common divisor of two numbers.

In the subsequent subsections, we explain how to run these examples.
Following these instructions assumes that WiSE and PyWiSE were built according to the `README` files in their respective directories.
In a nutshell, this means that you ran

```bash
cd Coq/
make
cd extraction
dune build
```

for WiSE, and

```bash
cd PyWiSE/
python3.10 -m venv venv
source venv/bin/activate
pip install -e .[dev,test]
```

for PyWiSE.

### GCD

The GCD example works both in WiSE and PyWiSE.
Note that, for historical reasons, the IMP syntax of the Coq/OCaml version is slightly different from the syntax presented in the [paper](https://arxiv.org/abs/2305.05570).
PyWiSE's IMP syntax precisely follows the definitions in the paper.

The code for the GCD problem in the "official" (PyWiSE/paper) syntax is

```
assert not a <= 0;
assert not b <= 0;
while not a == b do
  old_a = a ;
  old_b = b ;

  if a <= b then
    b = b - a
  else
    a = a - b
  fi;

  assert a >= 0 and b >= 0 and a < old_a or b < old_b
od
```

The notation for the same problem in Coq WiSE is

```
assume a > 0
assume b > 0
loop a != b {
  olda = a
  oldb = b

  if a <= b {
    b = b - a

  } else {
    a = a - b
  }

  assert a >= 0 and b >= 0 and (a < olda or b < oldb)
}
```

The `assume` statements used in the Coq version are not presented in the paper nor implemented in PyWiSE.



### Factorial

### Integer Square Root

## License

WiSE and PyWiSE have been released under the *MIT license* (see `Coq/COPYING` and `PyWiSE/COPYING`).
