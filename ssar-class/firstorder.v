Require Import Arith.

Goal forall x y z, x > y /\ y > z -> x > z /\ x > 0.
  
  
  intros. assert (z > 0).
  - admit.
  - pose gt_trans. firstorder.
  