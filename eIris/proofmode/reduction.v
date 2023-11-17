From elpi Require Import elpi.

From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments.
From iris.prelude Require Import options.

From eIris.proofmode.elpi Extra Dependency "reduction.elpi" as reduction.

Elpi Db reduction.db lp:{{
  pred reduction-rule o:constant.
}}.

Elpi Command EI.reduction.
Elpi Accumulate Db reduction.db.
Elpi Accumulate File reduction.
Elpi Accumulate lp:{{

  main [trm (global (const C))] :-
    add-reduction-rule C.

  main [trm (app [global (const C)| _ ])] :-
    add-reduction-rule C.

  main [] :-
    all-reductions CS,
    coq.say CS.
  
  main Args :-
    coq.say "EI.reduction only accepts constants, not" Args.

}}.
Elpi Typecheck.
Elpi Export EI.reduction.

(* base *)
EI.reduction (base.negb).
EI.reduction (base.beq).
EI.reduction (base.Pos_succ).
EI.reduction (base.ascii_beq).
EI.reduction (base.string_beq).
EI.reduction (base.positive_beq).
EI.reduction (base.ident_beq).

(* environments *)
EI.reduction (env_lookup).
EI.reduction (env_lookup_delete).
EI.reduction (env_delete).
EI.reduction (env_app).
EI.reduction (env_replace).
EI.reduction (env_dom).
EI.reduction (env_intuitionistic).
EI.reduction (env_spatial).
EI.reduction (env_counter).
EI.reduction (env_spatial_is_nil).
EI.reduction (envs_dom).
EI.reduction (envs_lookup).
EI.reduction (envs_lookup_delete).
EI.reduction (envs_delete).
EI.reduction (envs_snoc).
EI.reduction (envs_app).
EI.reduction (envs_simple_replace).
EI.reduction (envs_replace).
EI.reduction (envs_split).
EI.reduction (envs_clear_spatial).
EI.reduction (envs_clear_intuitionistic).
EI.reduction (envs_incr_counter).
EI.reduction (envs_split_go).
EI.reduction (envs_split).
EI.reduction (env_to_prop_go).
EI.reduction (env_to_prop).
EI.reduction (env_to_prop_and_go).
EI.reduction (env_to_prop_and).

(* PM list and option functions *)
EI.reduction (pm_app).
EI.reduction (pm_option_bind).
EI.reduction (pm_from_option).
EI.reduction (pm_option_fun).
