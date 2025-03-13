From elpi Require Import elpi.
From iris.prelude Require Import options.


Elpi Db induction.db lp:{{
  accumulate eIris/common/datatypes.

  pred inductive-pre o:gref, o:gref.
  pred inductive-mono o:gref, o:gref.
  pred inductive-fix o:gref, o:gref.
  pred inductive-unfold o:gref, o:gref, o:gref, o:gref, o:int.
  pred inductive-iter o:gref, o:gref.
  pred inductive-ind o:gref, o:gref.
  pred inductive-type o:gref, o:iind.
}}.
