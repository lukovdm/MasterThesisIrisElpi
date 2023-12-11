From elpi Require Import elpi.

Elpi Db induction.db lp:{{
  pred inductive-pre i:gref, o:gref, o:int.
  pred inductive-mono i:gref, o:gref.
  pred inductive-fix i:gref, o:gref.
  pred inductive-unfold i:gref, o:gref.
  pred inductive-iter i:gref, o:gref.
  pred inductive-ind i:gref, o:gref.
}}.
