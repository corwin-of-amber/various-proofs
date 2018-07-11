Set Implicit Arguments.    (* Allows us to use inference for dependent arguments *)

Require Import Reals.      (* Imports real arithmetic. *)
Delimit Scope R with Real.    (* Notice: due to the absence of overloading, from this *)
                           (* point on constants and operators are real-typed,     *)
Notation Real := R.           (* unless stated otherwise with the scope indicator '%' *)

Check 3 + 4.           (* : ℕ  (nat)  *)
Check (3 + 4) % R.     (* : ℝ  (Real) *)


Inductive Vec : nat -> Set :=
  VNil : Vec 0
| VCons : forall n, Real -> Vec n -> Vec (S n).

(* Some syntactic sugar *)
Notation "<< x , .. , y >>" := (VCons x .. (VCons y VNil) .. ).

Check << 5, 9, 6 >> .



Check VCons.
Print Implicit VCons.


Fail Definition c1 := repeat 1.
Definition c2 n := VCons (n:=n) 2.



Fixpoint repeat e n :=
  match n with
    0 => VNil
  | S k => VCons e (repeat e k)
  end.

Check repeat.


Compute repeat 4 5.
Eval simpl in repeat 4 5.


Check nat_rec.

Definition repeat' e :=
  nat_rec Vec VNil (fun x y => VCons e y).

Eval simpl in repeat' 4 5.


Check Vec_rec.


(* Notice that a return type is needed here *)
Fixpoint concat m n (v1 : Vec m) (v2 : Vec n) : Vec (m+n):=
  match v1 with
    VNil => v2
  | VCons x xs => VCons x (concat xs v2)
  end.

Definition ifz n (t1 t2 : Type) := match n with
                                   | 0 => t1
                                   | _ => t2 end.

Definition hd' n (v : Vec n) : ifz n unit R :=
  match v with
    VNil => tt
  | VCons x xs => x
  end.

Definition hd n (v : Vec (S n)) := hd' v.




Fixpoint Vec' n : Set :=
  match n with
    0 => unit
  | S k => R * Vec' k
  end.

Fixpoint vec_to_vec' n (v: Vec n) : Vec' n :=
  match v with
    VNil => tt
  | VCons x xs => (x, vec_to_vec' xs)
  end.



Fixpoint inner_product' n : Vec' n -> Vec' n -> Real :=
  match n with
    0 => fun _ _ => 0
  | S k => fun v1 v2 =>
            match v1, v2 with
              (x, xs), (y, ys) =>
              x * y + inner_product' k xs ys
            end
  end.

Fixpoint inner_product n (v1 v2 : Vec n) :=
  inner_product' n (vec_to_vec' v1) (vec_to_vec' v2).

Print inner_product.

Hint Unfold inner_product.

Example test_inner_product :
  inner_product <<1>> <<4>> = 4.
Proof. field. Qed.

Eval field in inner_product <<1>> <<4>>.


Check inner_product << 5, 9, 6 >> << 1, 3, 7 >>.
Fail Check inner_product << 9, 6 >> << 1, 3, 7 >>.




