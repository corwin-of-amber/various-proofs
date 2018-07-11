Inductive ord : (nat * nat) -> (nat * nat) -> Prop :=
  | ord_red1 : forall n n' m m',
    n < m -> ord (n, n') (m, m')
  | ord_red2 : forall n n' m',
    n' < m' -> ord (n, n') (n, m').

Require FunInd.
Require Recdef.
Require Import Wellfounded.

Check well_founded.
Check Fix.
Definition wf := @well_founded.


Fixpoint ack (n:nat) m : nat :=
        match n with
        | O => S m
        | S n' =>
            let fix ack' (m:nat) : nat :=
                match m with
                | O => ack n' 1
                | S m' => ack n' (ack' m')
                end
            in ack' m
        end.

