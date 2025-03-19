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
TODO: there are not the full instructions

The project can be built by first creating a Makefile using

```bash
coq_makefile -f _CoqProject -o Makefile
```

Next, the project can be built using

```bash
make
```

## Connection to the paper



## Folder structure

This project has the following structure

- **eIris**: This folder contains the proofmode, including Elpi source files.
  - **common**: Contains the Elpi source for the commonly used predicates.
    - **datatypes.v**: Datatypes necessary for storing properties in the Elpi inductive database.
    - **parser.v**: Parser for Iris introduction patterns.
    - **tokenize.v**: Tokenizer for Iris introduction patterns.
    - **stdpp.v**: Additional predicates and datatypes commonly used in other parts of our prototype.
  - **proofmode**: Contains the sources for the eIris proofmode.
    - **elpi**: The Elpi source code for the proofmode
      - **reduction.elpi**: Elpi sources for an extendible customizable reduction mechanism. Contains predicates to add terms to be considered while reducing, and predicates to reduce a term.
      - **iris_ltac.elpi**: Elpi bindings for specific Iris LTaC tactics for which a workaround could not be found. Also contains predicates which retrieve and set the anonymous hyp counter in the Iris context.
      - **mk_inductive.elpi**: Creates Inductive pre-fixpoint-function and fixpoint.
      - **proper_solver.elpi**: Contains the proper proof search algorithm.
      - **eiris_tactics.elpi**: Rewrite of the Iris LTaC tactics in Elpi.
      - **inductive_rules.elpi**: Generates the proof rules of an inductive and gives their proofs.
    - **base.v**: Rewritten Iris tactic lemmas for use in the Elpi variant of the tactics.
    - **proper.v**: Contains definition of signatures in Sozeau's Proper lifted to Iris, together with instances for the necessary Iris connectives.
  - **experiments**: Any experiments or examples using our tactics.
    - **channels.v**: Contains the linked list with delete nodes example from the paper.
    - **sets.v**: Contains several specifications of Sets using inductive predicates including the one from Section 3.
    - **rosetrees.v**: Contains the rose trees example from section 3.
    - **twp.v**: Contains the definition of the total weakest precondition and proofs of associated lemmas using our command and tactics.
    - **mll.v**: Contains a slightly different version of the `is_queue` as described in the paper, with fully specified insert and delete operations.
    - **arraylinkedlists.v**: Contains the representation predicate of a linked list where the nodes contain arrays. This allows for empty nodes, zero length arrays. The linked lists of arrays are represented by a Rocq list of all items in all arrays in order.
    - **indtest.v**: Contains basic examples for using the `Iris` command, and `iInduction` and `eiIntros` tactics.
- **Utils** Containing python scripts to generate tables
  - **Timing**: Contains a Python script and Coq source file which tests the speed of the intro pattern parser written in Elpi.
  - **generate_linecount_table.py** Generates LOC table as found in the paper

## Explanation of added introduction patterns

A few introduction patterns have been added or overloaded to improve the ergonomics of several tactics.

- `[|]`: When an inductive predicate is encountered, it is automatically unfolded. Then, the normal elimination rules are used.
- `[|]`: The conjunction and disjunction introduction pattern can take more than two options and are destructed assuming the terms are written right-associative.
- `*`: Destructs Iris existentials until none can be found at the head of the assumption.
- `**`: Destructs an inductive predicate and splits it into any possible branches. Does not further introduce the resulting assumptions.
