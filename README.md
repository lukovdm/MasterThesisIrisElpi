# Fixpoints in Higher-Order Separation Logic

The source code for the paper _Fixpoints in Higher-Order Separation Logic_

## Installing dependencies

This project is built for Rocq 8.20 with the associated version of the IPM and Rocq-Elpi.

This project is built using the opam package manager. 
When opam is installed, run the following to install all dependencies.

```bash
opam install . --deps-only
```

## Building the project

The project can be built by first creating a Makefile using

```bash
coq_makefile -f _CoqProject -o Makefile
```

Next, the project can be built using

```bash
make
```

## Folder structure

This project contains three main folders

- **eIris**: This folder contains the proofmode, including Elpi source files.
  - **common**: Contains the Elpi source for the commonly used predicates.
  - **proofmode**: Contains the sources for the eIris proofmode.
  - **experiments**: Any experiments or examples using our tactics.
    - **channels.v**: Contains the linked list with delete nodes example from the paper.
    - **indtest.v**: Contains basic examples for using the `Iris` command, and `iInduction` and `eiIntros` tactics.
    - **sets.v**: Contains several specifications of Sets using inductive predicates including the one from Section 3.
    - **twp.v**: Contains the definition of the total weakest precondition and proofs of associated lemmas using our command and tactics.
- **Utils** Containing python scripts to generate tables
  - **Timing**: Contains a Python script and Coq source file which tests the speed of the intro pattern parser written in Elpi.
  - **generate_linecount_table.py** Generates LOC table as found in the paper

## Explanation of added introduction patterns

A few introduction patterns have been added or overloaded to improve the ergonomics of several tactics.

- `[|]`: When an inductive predicate is encountered, it is automatically unfolded. Then, the normal elimination rules are used.
- `[|]`: The conjunction and disjunction introduction pattern can take more than two options and are destructed assuming the terms are written right-associative.
- `*`: Destructs Iris existentials until none can be found at the head of the assumption.
- `**`: Destructs an inductive predicate and splits it into any possible branches. Does not further introduce the resulting assumptions.
