# WiSE

**WiSE** (**W**hat **i**s **S**ymbolic **E**xecution) is a formally verified symbolic bug-finder for imperative programs.

> WiSE targets `IMP` a prototypical imperative programming language with integer arithmetic, variables, loops and conditions. WIP to extend it to more sophisticated features such as objects, arrays, pointers, threads etc

## Why Formally Verified ?

Finding bugs is crucial in any development cycle. In safety critical applications, it is also fundamental to hunt ALL the bugs! [Symbolic Execution (SE)]() is one of the many methods to achieve this goal by automating the search for bugs in source code. However, since automated bug-finders are program themselves, why should we trust them after all ? In particular, is it safe to assume that a program has no bug if our favorite bug-finders couldn't find any ? To answer this question, **WiSE** goes one step further and comes with a proof that is will *never miss any bug*! The development of WiSE and its mathematical proof are carried in the [Coq proof assistant]().

WiSE is *correct by construction*: it comes with strong mathematical guarantees about the quality and the accuracy of its results. These guarantees are of 3 kinds: *soundess*, *completeness* and *termination*.

### Soundess

WiSE is a *sound* bug-finder: whenever it finds a bug, it is really a bug and not just a false alarm. In other word, WiSE is never wasting your time :-).

### Completeness

WiSE is a *complete* bug-finder: if there is a bug in your program, the bug is eventually going to be detected (if you give WiSE enough time and resources). In turn, it means that if WiSE thinks your program is free of bug, you can believe it!

### Termination

Unfortunately, it is theoretically impossible to implement a generic bug-finder that is *sound* and *complete* and always terminates after a finite execution time for any arbitrary input program.
If such a bug-finder existed, it would be equivalent to deciding the so called *Halting Problem* and there are several mathematical proofs that it is impossible, no matter how hard we try!

Due to this theoretical limitation, WiSE does not always terminate and can be stuck in a never-ending loop. However, if WiSE signals that the analysis of its input program is terminated, then all the possible behaviors of the program have been explored.



## WiSE and the Coq proof assistant

WiSE is written in [Coq](), a purely functional programming language with a rich type system that allows to write program specifications, theorems and proofs. The correctness of the proofs can be verified by the Coq type-checker, thus leading to an incomparable level of reliability.

The source code of the bug-finder is written in Coq together with a theorem that claims soundness and completeness. This theorem is also proved in Coq and can be machine-checked. To turn WiSE into an executable program, the Coq sources are automatically extracted to an [OCaml]() program that can then be compiled into efficient machine code. WiSE has been programmed in a carefully chosen fragment of Coq such that the extracted OCaml code closely follows the structure of the verified Coq sources.

## Using WiSE

### Requirements

+ You need the last version of [opam](https://opam.ocaml.org/doc/Install.html).
+ Once opam is installed
  + ocaml 4.14.0
  + coq 8.13.2
  + dune 3.5.0
  + z3 4.11.2


### Compilation of the Coq sources

```
make
```
### Compiling the executable

```
cd extraction
dune build
```

### Running the demo on a small example program

```
cd extraction
dune exec ./bugfinder.exe
```

### Running the bugfinder on arbitrary programs

TODO: the parser and the CLI are not written yet
