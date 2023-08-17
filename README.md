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
Alternatively, you can [use our Docker container](#using-our-docker-container) that bundles all requirements and comes with readily built (Py)WiSE versions.

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

You must press Ctrl+C to terminate the execution.
The console will show many "Potential bug (CLEARED)" messages, which means that a path to a failed `assert` statement has been discovered but found to be infeasible.

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

In contrast to WiSE, PyWiSE contains a depth limit to ensure termination.
Thus, you do not have to interrupt the search manually if no bug was discovered.
The command-line interface of PyWiSE offers an `-n` parameter to change the depth limit (we use this parameter in the [integer square root example](#integer-square-root)).

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
  Path:          (a > b) & (b > 0) & Ne(a, 0)
  Example Input: a := 2, b := 1
  Store:         {}{old_a -> a}{old_b -> b}{a -> a + b}
BUG FOUND
  Path:          (a > 0) & (a < b) & Ne(b, 0) & (b < 2*a)
  Example Input: a := 2, b := 3
  Store:         {}{old_a -> a}{old_b -> b}{b -> -a + b}{old_a -> a}{old_b -> -a + b}{a -> b}
BUG FOUND
  Path:          (a > 0) & (a < b) & Ne(b, 0) & (b > 2*a) & (b < 3*a)
  Example Input: a := 2, b := 5
  Store:         {}{old_a -> a}{old_b -> b}{b -> -a + b}{old_a -> a}{old_b -> -a + b}{b -> -2*a + b}{old_a -> a}{old_b -> -2*a + b}{a -> -a + b}
```

The displayed expressions are not in IMP's expression language since the `simplify` option, which is turned on by default in PyWiSE, uses sympy to output compressed terms to the user.

### Integer Square Root

In this example, we compute the integer square root of a strictly positive number.
The algorithm must calculate a number's square multiple times.
Since IMP's syntax does not know multiplication, we must compute the square `s` of a number `r` by repeated addition inside a loop:

```
s = r;
i = 1;
while i < r do
  s = s + r;
  i = i + 1
od
```

To relieve us from spelling out this primitive operation multiple times in the code, PyWiSE provides a simple macro mechanism.
Thus, we can write:

```
macro square(s, r, i)
begin
  s = r;
  i = 1;
  while i < r do
   s = s + r;
   i = i + 1
  od
end
```

and use the macro like `square(_s, r, r, _i)` in the code.
The effect is that the statement `square(_s, r, r, _`i)` is replaced by the macro content after substituting the formal parameters.
Macros can only call other macros that are defined earlier in a file.
Consequently (and because they are *inlined* after pre-processing), they cannot be (mutually) recursive.
We refer to [the README of PyWiSE](PyWiSE/README.md) for more information on macros.

Since macros are only implemented in PyWiSE's frontend, the integer square root example with macros does not work in (Coq) WiSE.
Interested users may still use WiSE for this example after manually inlining the `square` macro.

To analyze the example with PyWiSE, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -n 100 -a "x > 0" integer_sqrt_correct.imp
```

The `-n` parameter controls the number of symbolic execution states the analysis produces and inspects.

The expected output of this run is

```
Analyzing file integer_sqrt_correct.imp

No bug found at depth 100.
```

The "buggy" version of integer square root replaces the line `should be _s > x` by `while _s < x do`.
To analyze the mutated example, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -n 100 -a "x > 0" integer_sqrt_buggy.imp
```

The expected output of this run is

```
Analyzing file examples/integer_sqrt_buggy.imp

BUG FOUND
  Path:          (x <= 2) & (x > 1) & Ne(x, 0) & ((x > 0) | (x < -3/2))
  Example Input: x := 2
  Store:         {}{r -> x}{_s -> x}{_i -> 1}{_s -> 2*x}{_i -> 2}{_s_1 -> x}{_i -> 1}{_s_1 -> 2*x}{_i -> 2}{_s_2 -> x + 1}{_i -> 1}{_s_2 -> 2*x + 2}{_i -> 2}{_s_2 -> 3*x + 3}{_i -> 3}
```

### Factorial

The factorial example uses three macros:
One for division, one for multiplication, and one for the specification (postcondition).
The main code reads

```
assert n >= 2;

factorial = 1;
i = 1;
while i <= n do
  mul(mul_result, factorial, i, _i);
  factorial = mul_result;
  i = i + 1
od;

factorial_spec(n, factorial, _i, _d, _m)
```

To analyze the example with PyWiSE, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -n 100 -a "n >= 2" factorial_correct.imp
```

The `-n` parameter controls the number of symbolic execution states the analysis produces and inspects.

The expected output of this run is

```
Analyzing file factorial_correct.imp

No bug found at depth 100.
```

The "buggy" version of integer square root replaces the line `should be _s > x` by `while _s < x do`.
To analyze the mutated example, run (from the project's main directory)

```bash
cd PyWiSE/
source venv/bin/activate
cd examples/
wise -n 100 -a "n >= 2" factorial_buggy.imp
```

The expected output of this run is

```
Analyzing file factorial_buggy.imp

BUG FOUND
  Path:          (n >= 2) & (n < 3)
  Example Input: n := 2
  Store:         {}{factorial -> 1}{i -> 1}{mul_result -> 1}{_i -> 1}{factorial -> 1}{i -> 2}{mul_result -> 1}{_i -> 1}{mul_result -> 3}{_i -> 2}{factorial -> 3}{i -> 3}{_i -> 2}{_m -> 3}{_d -> 0}{_d -> 1}{_m -> 1}
```

## Using our Docker Container

Our Docker container contains the complete infrastructure for running (Py)WiSE (Coq, Python 3.10, Z3, etc.).
Furthermore, WiSE and PyWiSE are pre-built in the image.
Thus, you can start experimenting with our tools and examples without interruptions!

To retrieve and start the docker container, you need a working Docker installation, and the Docker daemon must be running.
Then, type in a terminal

```bash
docker pull dsteinhoefel/wise
docker run -it --name wise dsteinhoefel/wise
```

Afterward, you should see the bash prompt of the Docker container and should be able to follow the instructions for [running the examples](#running-the-examples-from-the-paper).

## License

WiSE and PyWiSE have been released under the *MIT license* (see `Coq/COPYING` and `PyWiSE/COPYING`).
