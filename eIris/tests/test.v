Require Import Utf8.

Goal ∀ P, P -> P.
Admitted.

Goal ∀ P Q, P -> Q -> Q.
Admitted.

Goal ∀ P R Q, P -> R -> Q -> P.
Admitted.

Goal ∀ P, P -> (if true then P else False).
