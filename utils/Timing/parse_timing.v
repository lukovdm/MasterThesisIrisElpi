From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction intro_patterns.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.
(* From eIris.proofmode Require Import split. *)

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.
From eIris.common Extra Dependency "parser.elpi" as parser.

Elpi Tactic print_args.
Elpi Accumulate File stdpp.
Elpi Accumulate File tokenize.
Elpi Accumulate File parser.
Elpi Accumulate lp:{{

  pred test i:string, o:list intro_pat.
  test S IPS :-
    tokenize S T, !,
    coq.say "tokenized",
    parse_ipl T IPS.

  pred readLineFile i:string, o:string.
  readLineFile Filename Output :-
    open_in Filename FileStream,
    input_line FileStream Output,
    close_in FileStream.
}}.

Ltac time_constr1 tac :=
  let eval_early := match goal with _ => restart_timer "(depth 1)" end in
  let ret := tac () in
  let eval_early := match goal with _ => finish_timing ( "Tactic evaluation" ) "(depth 1)" end in
  ret.

Goal True.
    let v := time_constr
        ltac:(fun _ =>
            let y := time_constr1 ltac:(fun _ => intro_pat.parse 
            "") in
            y) in
    pose v.
(* results for 8: Ran for 1.119 secs *)

(* Elpi Trace Browser. *)
Elpi Query lp:{{
  readLineFile "/home/luko/Uni/7/MThesis/MasterThesisIris/experiments/intro_pattern_5.txt" S,
  std.time (test S _) T1,
  coq.say "run 1" T1,
  std.time (test S _) T2,
  coq.say "run 2" T2,
  std.time (test S _) T3,
  coq.say "run 3" T3,
  std.time (test S _) T4,
  coq.say "run 4" T4,
  coq.say "runs" T1 T2 T3 T4 {calc ((T1 + T2 + T3 + T4)/4.0)}.
}}.
(* results for 8 with backtracking: runs 47.934084 47.418096 47.257010 47.270303 47.469873 *)
(* results for 8 without backtracking: runs 0.236785 0.236670 0.243691 0.247548 0.241174 *)
