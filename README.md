# Fixpoints in Higher-Order Separation Logic

The source code for the paper _Fixpoints in Higher-Order Separation Logic_

## Stetting up the project

**Step 1: Installing Opam**

This project makes use of the opam package manager. [Install](https://opam.ocaml.org/doc/Install.html) at least version 2.0 and activate using the following commands

```bash
opam init
eval $(opam env)
```

**Step 2: Create a switch**

Create and load a local switch 

```bash
opam switch create --no-install . ocaml-variants.4.14.1+options
eval $(opam env)
```

**Step 3: Installing dependencies**

Install the dependencies by running the following command

```bash
opam install . --deps-only
```

**Step 4: Building the project and checking the formalizations**

The project can be built by first creating a Makefile using

```bash
coq_makefile -f _CoqProject -o Makefile
```

Next, the project can be built using

```bash
make -j <cpu cores>
```
Where you can fill in the amount of cores to use in `<cpu cores>`.

## Connections to the paper
We give a mapping between section and examples in the paper and files found in this artifact.

**Section 1: Introduction**

* Application #1: `is_del_list`
  
  It can be found in `eIris/experiments/dellists.v`

**Section 3: Data Structure Verification**

* First example, delete lists with a parameter: `is_list_with_tl`

  It can be found in `eIris/experiments/dellists.v`

* Second example, BSTs: `is_search_tree`

  It can be found in `eIris/experiments/sets.v`

* Third example, rose trees: `is_ho_list` and `is_rose_tree`

  They can be found in `eIris/experiments/rosetrees.v`

**Section 4: Total Program Correctness**

* Proof of the total correctness of `lookup` Hoare Triple

  It can be found in `eIris/experiments/dellists.v` as the lemma `lookup_spec`.

**Section 5: Prototype Command and Tactic in Rocq-Elpi**

_Section 5.1: Constructing the fixpoint_

This section formalized in the file `eIris/proofmode/elpi/mk_inductive.elpi`. The `Iris` command is defined in `eIris/proofmode/inductive.v`. The examples are found as follows:

* The definitions `is_list_with_tl_pre` and `is_list_with_tl`

  Are obtained by calling `Print is_list_with_tl_pre` and `Print is_list_with_tl` in `eIris/experiments/dellists.v`.

_Section 5.2: Variadic Monotonicity_

This section is formalized in the files `eIris/proofmode/proper.v` and `eIris/proofmode/elpi/proper_solver.elpi`. 

* The proper for `is_list_with_tl`:

  Is obtained by calling `Check is_list_with_tl_pre_mono` in `eIris/experiments/dellists.v`. Note that this uses the pointwise signature combinator as referenced in footnote 2 of the paper.

_Section 5.3: Generating the Monotonicity Proof and Proof Rules_

This section is formalized in the files `eIris/proofmode/elpi/eiris_tactics.elpi`, `eIris/proofmode/elpi/inductive_rules.elpi`, and `eIris/proofmode/inductive.v`.

* The lemma `tac_wand_intro`

  It can be found in **TODO**

* All tactics given in this section: `refine-igoal-with`, `eiIntro-ident`, and `eiIntro-fresh`

  They can be found in `eIris/proofmode/elpi/eiris_tactics.elpi`

* The definition of `pm-reduce`

  It can be found in `eIris/proofmode/elpi/reduction.elpi`

_Section 5.4: The iInduction tactic_

This section is formalized in `eIris/proofmode/inductiveDB.v` and `eIris/proofmode/inductionTac.v`.

_Section 5.5: Evaluation_

The lines of code are generated from `utils/generate_linecount_table.py`. Reimplementing the total weakest precondition can be found in **TODO**



## Explanation of Added tactics and commands
We have added an `Iris` command, `iInduction` tactic, and bindings for the rewritten Iris tactics: `eiStratProof`, `eiAppli`, `eiIntros` and `eiDestruct`.

### The `Iris` command
The `Iris` command takes as argument an inductive instance, where the type of the inductive is in some Iris `PROP`. The constructors should use the magic wand (`-∗`) instead of implications (`->`). The type of the inductive can contain optional `Non-Expansive` arguments. An example can be found in the `eIris/experiments/twp.v` file. Arguments can be marked as non-expansive from the end of the type by using `-n>` instead of `->`.

The `Iris` command can get the optional `#[debug]` argument, giving both debug prints and with it, timing information. There also exist feature flags to disable parts of the inductive generation, e.g., `nounfold`, `noiter` and `noind`.

### The `iInduction` tactic
The `iInduction` can be called either with a string containing the name of an Iris hypothesis and an introduction pattern, or just the name of the hypothesis:

- `iInduction "H1" as "[ ... | ... | ... ]".`
- `iInduction "H1".`

If no introduction pattern is given it destructs the generated hypothesis into goals for each constructor.

### Explanation of added introduction patterns

A few introduction patterns have been added or overloaded to improve the ergonomics of several tactics.

- `[|]`: When an inductive predicate is encountered, it is automatically unfolded. Then, the normal elimination rules are used.
- `[|]`: The conjunction and disjunction introduction pattern can take more than two options and are destructed assuming the terms are written right-associative.
- `*`: Destructs Iris existential quantifiers until none can be found at the head of the assumption.
- `**`: Destructs an inductive predicate and splits it into any possible branches. Does not further introduce the resulting assumptions.

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
    - **reduction.v**: Defines the Rocq-Elpi tactic itself and adds all Iris reduction terms.
    - **startProof.v**: Binds the Elpi start proof tactic to a Rocq tactic.
    - **apply.v**: Binds the Elpi eiApply tactic to a Rocq tactic.
    - **tactics.v**: Binds the Epli eiIntro and eiDestruct to Rocq tactics.
    - **inductiveDB.v**: Defines the Elpi DB in which the fixpoint is connected to its proof rules and properties.
    - **inductive.v**: Defines the `Iris` inductive command.
    - **inductionTac.v**: Defines the `iInduction` tactic.
  - **experiments**: Any experiments or examples using our tactics.
    - **dellist.v**: Contains the linked list with delete nodes example from the paper.
    - **sets.v**: Contains several specifications of Sets using inductive predicates including the one from Section 3.
    - **rosetrees.v**: Contains the rose trees example from section 3.
    - **twp.v**: Contains the definition of the total weakest precondition and proofs of associated lemmas using our command and tactics.
    - **mll.v**: Contains a slightly different version of the `is_queue` as described in the paper, with fully specified insert and delete operations.
    - **arraylinkedlists.v**: Contains the representation predicate of a linked list where the nodes contain arrays. This allows for empty nodes, zero length arrays. The linked lists of arrays are represented by a Rocq list of all items in all arrays in order.
    - **indtest.v**: Contains basic examples for using the `Iris` command, and `iInduction` and `eiIntros` tactics.
- **Utils** Containing python scripts to generate tables
  - **Timing**: Contains a Python script and Coq source file which tests the speed of the intro pattern parser written in Elpi.
  - **generate_linecount_table.py** Generates LOC table as found in the paper
