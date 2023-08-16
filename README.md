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
assert not a <= 0 ;
assert not b <= 0 ;
while not a == b do
  old_a = a ;
  old_b = b ;

  if a <= b then
    b = b - a
  else
    a = a - b
  fi ;

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

The `assume` statement type used in the Coq version is not presented in the paper nor implemented in PyWiSE.

To analyze the GCD example with WiSE, run (from the project's main directory)

```bash
cd Coq/extraction/_build/default/
./bugfinder.exe -i gcd_correct.imp
```

The expected output, assuming you press "N" or Enter to end the session after the respective prompt, is

```
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[x] => Found bug (((((not (a <= 0)) and (not (b <= 0))) and (not (a = b))) and (a <= b)) and (((0 <= a) and (0 <= (b - a))) and (not ((a <= a) and (b <= (b - a))))))
Do you want to continue [y/N]

Ending the session
```

TODO @Arthur: No, there should be no bug :) What happens here?

To analyze the example with PyWiSE, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -a "a > 0 and b > 0" gcd_correct.imp
```

The `-a` flag allows to add an *assumption* on program inputs to be considered during symbolic execution.
It replaces the `assume` statement type from the Coq version.
A bug would be reported without those premises since the `assert` statements could fail.

The expected output of this run is

```
Analyzing file gcd_correct.imp

No bug found at depth 50.
```

To assert that our prototypes *can* find bugs if there are any, we created an intentionally "buggy" version of GCD:

```
assert not a <= 0 ;
assert not b <= 0 ;
while not a == b do
  old_a = a ;
  old_b = b ;

  if a <= b then
    b = b - a
  else
    a = a + b  # should be a - b
  fi ;

  assert a >= 0 and b >= 0 and a < old_a or b < old_b
od
```

To analyze the *buggy* GCD example with WiSE, run (from the project's main directory)

```bash
cd Coq/extraction/_build/default/
./bugfinder.exe -i gcd_buggy.imp
```

The expected output, assuming you press "N" or Enter to end the session after the respective prompt, is

```
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[o] => Pending
[x] => Found bug (((((not (a <= 0)) and (not (b <= 0))) and (not (a = b))) and (a <= b)) and (((0 <= a) and (0 <= (b - a))) and (not ((a <= a) and (b <= (b - a))))))
Do you want to continue [y/N]

Ending the session
```

To analyze the example with PyWiSE, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -a "a > 0 and b > 0" gcd_buggy.imp
```

The expected output of this run is

```
Analyzing file gcd_buggy.imp

BUG FOUND
  Path:          0 <= a and not (0 == a) and 0 <= b and not (0 == b) and not (a <= 0) and not (b <= 0) and not (a == b) and not (a <= b) and not (0 <= (a + b) and 0 <= b and b <= 0 and not (b == 0))
  Example Input: a := 2, b := 1
  Store:         {}{old_a -> a}{old_b -> b}{a -> (a + b)}
BUG FOUND
  Path:          0 <= a and not (a == 0) and 0 <= b and not (b == 0) and not (a <= 0) and not (b <= 0) and not (a == b) and a <= b and not (not (0 <= a and 0 <= (b - a) and a <= a and not (a == a)) and not ((b - a) <= b and not ((b - a) == b))) and not (a == (b - a)) and not (a <= (b - a)) and not (not (not (0 <= (a + (b - a)) and 0 <= (b - a) and (a + (b - a)) <= a and not ((a + (b - a)) == a)) and not ((b - a) <= (b - a) and not ((b - a) == (b - a)))))
  Example Input: a := 2, b := 3
  Store:         {}{old_a -> a}{old_b -> b}{b -> (b - a)}{old_a -> a}{old_b -> (b - a)}{a -> (a + (b - a))}
BUG FOUND
  Path:          0 <= a and not (a == 0) and 0 <= b and not (b == 0) and not (a <= 0) and not (b <= 0) and not (a == b) and a <= b and not (not (0 <= a and 0 <= (b - a) and a <= a and not (a == a)) and not ((b - a) <= b and not ((b - a) == b))) and not (a == (b - a)) and a <= (b - a) and not (not (0 <= a and 0 <= ((b - a) - a) and a <= a and not (a == a)) and not (((b - a) - a) <= (b - a) and not (((b - a) - a) == (b - a)))) and not (a == ((b - a) - a)) and not (a <= ((b - a) - a)) and not (not (not (0 <= (a + ((b - a) - a)) and 0 <= ((b - a) - a) and (a + ((b - a) - a)) <= a and not ((a + ((b - a) - a)) == a)) and not (((b - a) - a) <= ((b - a) - a) and not (((b - a) - a) == ((b - a) - a)))))
  Example Input: a := 2, b := 5
  Store:         {}{old_a -> a}{old_b -> b}{b -> (b - a)}{old_a -> a}{old_b -> (b - a)}{b -> ((b - a) - a)}{old_a -> a}{old_b -> ((b - a) - a)}{a -> (a + ((b - a) - a))}
```

### Factorial

### Integer Square Root

## Using our Docker Container

TODO

## License

WiSE and PyWiSE have been released under the *MIT license* (see `Coq/COPYING` and `PyWiSE/COPYING`).
