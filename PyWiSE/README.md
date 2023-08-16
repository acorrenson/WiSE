# PyWiSE: A Python Twin of the Verified Symbolic Bug Finder WiSE

PyWiSE is a re-implementation of the (verified) Coq version of WiSE in Python. It
features a command-line interface and parser to symbolically execute IMP programs. All
code, with the exception of the parser and CLI code, closely mirror the Coq
implementation. To demonstrate this, the original Coq code is provided as
inline-comments close to the code mirroring it.

The relevant files are:

- `streams.py`, mirroring `streams.v`&mdash;a small library for infinite streams.
- `imp.py`, mirroring `imp.v`&mdash;the IMP programming language.
- `symex.py`, mirroring `symex.v`&mdash;symbolic evaluation of expressions.
- `bugfinder.py`, mirroring `bugfinder.v`&mdash;the implementation of the bug finder.

## Macros

For convenience, PyWiSE supports simple macro definitions which are inlined in the
IMP program. Macros must be defined at the beginning of an IMP file and are not
separated by semicolons either from each other or the remaining program. They can call
other macros defined *before* (which implies that they cannot be (mutually) recursive).
An example program using a macro is:

```
macro subadd1(x, y)
begin
  x = x - y;
  x = x + 1
end
subadd1(a, b);
x = 17 
```

which expands to

```
a = a - b;
a = a + a;
x = 17
```

Note that macro "calls" are "statements," so you cannot invoke a macro inside an 
expression.


## Installation

PyWiSE project requires Python 3.10 or higher. It is on PyPi; a simple
`pip install wise-se` suffices to install the symbolic executor in the current Python
environment.

If you want to build the project locally, we recommend using a virtual environment:

```shell
cd /path/to/PyWiSE
python3.10 -m venv venv
source venv/bin/activate
pip install .[dev,test]
```

Either way, the `wise` command should now be available on your command line. You can
test it on the examples in the `examples/` directory, e.g.:

```shell
$ wise examples/gcd_buggy.imp
Analyzing file examples/gcd_buggy.imp

BUG FOUND
  Path:          a <= 0
  Example Input: a := 0
  Store:         {}
BUG FOUND
  Path:          not (a <= 0) and b <= 0
  Example Input: a := 1, b := 0
  Store:         {}
BUG FOUND
  Path:          not (a <= 0) and not (b <= 0) and not (a == b) and not (a <= b) and not (0 <= (a + b) and 0 <= b and b <= 0 and not (b == 0))
  Example Input: a := 2, b := 1
  Store:         {}{old_a -> a}{old_b -> b}{a -> (a + b)}
...
```

The first two bugs are failing assertions on the input; the third one is a "real" bug.
For some examples, you might have to increase the number of generated symbolic states,
as in `wise -n 100 ...`.

Enter `wise -h` for a short help text on the available options.

## Copyright and License

Copyright © 2023 Arthur Correnson and Dominic Steinhöfel.

PyWiSE is released under the MIT License (see [COPYING](COPYING)).
