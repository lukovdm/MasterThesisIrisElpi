files = {
    "Common": ["eIris/common/stdpp.elpi"],
    "Iris tactics": [
        "eIris/common/parser.elpi",
        "eIris/common/tokenize.elpi",
        "eIris/proofmode/elpi/iris_ltac.elpi",
        "eIris/proofmode/elpi/eiris_tactics.elpi",
        "eIris/proofmode/elpi/reduction.elpi",
        "eIris/proofmode/reduction.v",
        "eIris/proofmode/tactics.v",
    ],
    "Generate fixpoint": [
        "eIris/proofmode/elpi/mk_inductive.elpi",
        "eIris/proofmode/inductive.v",
    ],
    "Monotone proof search": [
        "eIris/proofmode/proper.v",
        "eIris/proofmode/elpi/proper_solver.elpi",
    ],
    "Inductive rules": [
        "eIris/proofmode/elpi/inductive_rules.elpi",
    ],
    "Induction tactic": [
        "eIris/proofmode/inductionTac.v",
    ],
}

if __name__ == "__main__":
    print("\\begin{tabular}{rll}")
    print("\\toprule")
    print("Category & Rocq Line count & Elpi Line count \\\\")
    print("\\midrule")
    for category, filenames in files.items():
        count_elpi = 0
        count_coq = 0
        for filename in filenames:
            in_coq = filename.endswith(".v")
            with open(filename, "r") as f:
                for line in f:
                    if (
                        line.strip().startswith("%")
                        or line.strip() == ""
                        or "if-debug" in line
                    ):
                        continue

                    if r"Elpi Accumulate lp:{{" in line:
                        in_coq = False
                    elif line.strip() == r"}}.":
                        in_coq = True

                    if in_coq:
                        count_coq += 1
                    else:
                        count_elpi += 1
        print(f"{category} & {count_coq} & {count_elpi} \\\\")
    print("\\bottomrule")
    print("\\end{tabular}")
