# Extending the Iris Proof Mode with Inductive Predicates using Elpi

The source code for the master thesis _Extending the Iris Proof Mode with Inductive Predicates using Elpi_

## Installing dependencies

This project is build for Coq 8.19 with the associated version of the IPM and Coq-Elpi.

This project is build using the opam package manager. When opam is installed, run the following to install all dependencies

```bash
opam install . --deps-only
```

To run the experiments, the Iris heaplang package is also neccesary.

```bash
opam install coq-iris-heap-lang
```

## Building the project

The project can be build by first creating a Makefile using

```bash
coq_makefile -f _CoqProject -o Makefile
```

Next the project can be build using

```bash
make
```

## Folder structure

This project contains three main folders

- **eIris**: This folder contains the proofmode, including elpi source files.
  - **common**: Contains the elpi source for commonly used predicate.
  - **proofmode**: Contains sources for the eiIris proofmode.
- **experiments**: Any experiments or examples using our tactics.
  - **Timing**: Contains a python script and coq source file which test the speed of the intro pattern parser written in Elpi.
  - **indtest.v**: Contains basic examples for using the `ei.Ind` and `eiIntros` tactics.
  - **sets.v**: Contains the definition of `is_MLL`, the representation predicate for marked linked lists. And several proofs of specifications concerning MLL.
  - **twp.v**: Contains the definnition of the total weakest precondition and proofs of associated lemmas using our system.
- **Latex**: Contains the latex source for the thesis, project proposal and (WIP) presentation.

## Explanation of added introduction patterns

A few introduction patterns have been added or overloaded to improve the ergonomics of several tactics.

- `[|]`: When an inductive predicate is encoutered it is automatically unfolded.
- `[|]`: The conjuction and disjuction introduction pattern can take more then two options and are destructed assuming the terms are written right associative.
- `*`: Destructs Iris existensials until none can be found at the head of the assumption.
- `**`: Destructs an inductive predicate and splits into the possible branches. Does not further introduce the resulted assumptions.
