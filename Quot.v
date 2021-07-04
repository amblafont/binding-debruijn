(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Axiom of extensionality *)

Axiom extensionality : forall (X Y : Type) (f g : X -> Y),
  (forall x, f x = g x) -> f = g.


(** * Equivalence relations and quotients *)


Set Implicit Arguments.

(* Require Import Extensionality. *)

Implicit Type X Y Z W : Type.

(** ** Equivalence relations *)

Record Eqv (X : Type) : Type := {
  eqv_data :> X -> X -> Prop;
  eqv_rfl : forall x, eqv_data x x;
  eqv_sym : forall x y, eqv_data y x -> eqv_data x y;
  eqv_trs : forall x y z,
    eqv_data x y -> eqv_data y z -> eqv_data x z
}.


Lemma eq_eqv : forall X (r : Eqv X) x y, x = y -> r x y.
Proof.
destruct 1. apply eqv_rfl.
Qed.


(** ** Quotients *)

Parameter quotient : forall (X : Type) (r : Eqv X), Type.
Arguments quotient : clear implicits.

Declare Scope quotient.

Infix "//" := quotient
  (at level 45, right associativity) : quotient.
Open Scope quotient.

Parameter class : forall (X : Type) (r : Eqv X), X -> X//r.
Arguments class [X].
Notation "x / r" := (class r x) : quotient.

Axiom class_eq : forall (X : Type) (r : Eqv X) (x y : X),
  r x y -> x/r = y/r.

Axiom class_rel : forall (X : Type) (r : Eqv X) (x y : X),
  x/r = y/r -> r x y.

Axiom class_ind : forall (X : Type) (r : Eqv X) (P : X // r -> Prop),
  (forall x : X, P (x / r)) -> forall x : X // r, P x.

Parameter factor : forall (X : Type) (r : Eqv X) Y (f : X -> Y)
  (Hf : forall x y, r x y -> f x = f y),
  X//r -> Y.
Arguments factor [X] r [Y].

Axiom factorize : forall (X : Type) (r : Eqv X) (Y : Type) (f : X -> Y)
  (H : forall x y, r x y -> f x = f y),
    forall x ,  factor r f H (x/r) = f x.

Lemma factor_extens : forall X (r : Eqv X) Y (f g : X -> Y)
  (Hf : forall x y, r x y -> f x = f y)
  (Hg : forall x y, r x y -> g x = g y)
  (H : forall x, f x = g x),
  forall x, factor r f Hf x = factor r g Hg x.
Proof.
intros.
apply (class_ind (fun x => factor r f Hf x = factor r g Hg x)).
intros.
do 2 rewrite factorize. trivial.
Qed.



Section Factor1.

Variable (X : Type) (rX : Eqv X) (Y : Type) (rY : Eqv Y) (f : X -> Y).
Hypothesis Hf : forall x y, rX x y -> rY (f x) (f y).

Definition factor1 : X // rX -> Y // rY.
Proof.
apply (factor rX (fun x => f x / rY)).
abstract auto using class_eq.
Defined.

Lemma factorize1 : forall x, factor1 (x / rX) = f x / rY.
Proof.
unfold factor1.
intros. rewrite factorize. reflexivity.
Qed.

End Factor1.

Arguments factor1 [X] rX [Y].
Arguments factorize1 [X] rX [Y] rY.

Lemma factor1_extens : forall X (rX : Eqv X) Y (rY : Eqv Y) (f g : X -> Y)
  (Hf : forall x y, rX x y -> rY (f x) (f y))
  (Hg : forall x y, rX x y -> rY (g x) (g y))
  (H : forall x, rY (f x) (g x)),
  forall x, factor1 rX rY f Hf x = factor1 rX rY g Hg x.
Proof.
intros. unfold factor1.
apply factor_extens. auto using class_eq.
Qed.

Section Factor2.

Variable (X : Type) (rX : Eqv X) (Y : Type) (rY : Eqv Y) (Z : Type) (rZ : Eqv Z).
Variable f : X -> Y -> Z.

Hypothesis Hf : forall x y z w,
  rX x y -> rY z w -> rZ (f x z) (f y w).

Let h  (x : X) : Y // rY -> Z // rZ.
Proof.
intro. apply (factor1 rY rZ (f x)). abstract auto using eqv_rfl.
assumption.
Defined.

Remark rmk : forall x y, rX x y -> h x = h y.
Proof.
unfold h. intros. apply extensionality.
apply (class_ind
  (fun x0 =>
    factor1 rY rZ (f x) (h_subproof x) x0 = factor1 rY rZ (f y) (h_subproof y) x0)).
intros.
do 2 rewrite factorize1. auto using class_eq, eqv_rfl.
Qed.

Definition factor2 : X // rX -> Y // rY -> Z // rZ.
Proof.
apply (factor rX h). exact rmk.
Defined.

Lemma factorize2 : forall x y,
  factor2 (x / rX) (y / rY) = f x y / rZ.
Proof.
unfold factor2, h. intros.
rewrite factorize. rewrite factorize1. auto.
Qed.

End Factor2.

Arguments factor2 [X] _ [Y] _ [Z].
Arguments factorize2 [X] _ [Y] _ [Z].


Lemma factor2_extens :
  forall X (rX : Eqv X) Y (rY : Eqv Y) Z (rZ : Eqv Z)
  (f : X -> Y -> Z)
  (Hf : forall x y z w, rX x y -> rY z w -> rZ (f x z) (f y w))
  (g : X -> Y -> Z)
  (Hg : forall x y z w, rX x y -> rY z w -> rZ (g x z) (g y w))
  (H : forall x y, rZ (f x y) (g x y)) x y,
  factor2 rX rY rZ f Hf x y = factor2 rX rY rZ g Hg x y.
Proof.
intros until 1.
apply (class_ind
  (fun x => forall (y : Y // rY),
     factor2 rX rY rZ f Hf x y = factor2 rX rY rZ g Hg x y)).
intro.
apply (class_ind
  (fun y => factor2 rX rY rZ f Hf (x/rX) y = factor2 rX rY rZ g Hg (x/rX) y)).
intro. do 2 rewrite factorize2. auto using class_eq, eqv_rfl.
Qed.

(**

Additions to the original file

 *)
Require Import Lib.
Require Import Arith.
Section relvec.

  Context (A B : Type)(R : B -> B -> Prop) .
Inductive rel_vec : forall (l : list A),
    vec B l -> vec B l -> Prop :=
  nil_rel_vec :  rel_vec NilV NilV
| cons_rel_vec : forall n l t t' v v', rel_vec (l := l)  v v' -> R t t' -> rel_vec (ConsV n t v)(ConsV n t' v').

Lemma rel_vec_rfl (rx : forall x, R x x) l (v : vec B l) : rel_vec v v.
  induction v.
  - constructor.
  - constructor; auto.
Qed.
  End relvec.

Fixpoint vec_quot_ind
         {A B : Type}{R : Eqv B}{l : list A}
         (P : vec (B // R) l -> Prop)
         (Pquot : forall (v : vec B l), P (vec_map (fun _ => class R) v)) 
         (v : vec (B // R) l) : P v.
Proof.
  destruct v as [|a l b v].
  - apply (Pquot NilV).
  - cbn.
    revert v b.
    unshelve refine (vec_quot_ind _  _ _ _ _  _).
    +  intros v b.
       revert b v.
       unshelve refine (class_ind _ _).
       exact (fun b v => Pquot (ConsV a b v )).
Qed.

Fixpoint vec_quot_out (A B C : Type)(R : Eqv B)(l : list A)[f : vec B l -> C]
      (compat_f : forall b b', rel_vec R b b' -> f b = f b')
      (v : vec (B // R) l) : C.
  destruct v as [|a l b v].
  - exact (f NilV).
  - cbn.
    revert v b.
    unshelve refine (vec_quot_out _ _ _ _ _ _  _).
    +  intros v b.
       revert b v.
       unshelve refine (factor R _ _).
        * exact (fun b v => f (ConsV a b v )).
        * intros b b' r.
          cbn.
          apply extensionality.
          intro v.
          apply compat_f.
          --  apply cons_rel_vec.
              ++ apply rel_vec_rfl, eqv_rfl.
              ++ assumption.
    + intros v v' rb.
      cbn.
      apply extensionality.
      apply class_ind.
      intro b.
      cbn.
      rewrite factorize.
      apply compat_f.
      constructor.
      * assumption.
      * apply eqv_rfl.
Defined.

Fixpoint vec_quot_out_proj (A B C : Type)(R : Eqv B)(l : list A)(f : vec B l -> C)
      (compat_f : forall b b', rel_vec R b b' -> f b = f b')
      (v : vec B l) :
  vec_quot_out compat_f (vec_map (fun _ => class R) v) = f v.
Proof.
  destruct v.
  - reflexivity.
  - cbn.
    rewrite vec_quot_out_proj.
    rewrite factorize.
    reflexivity.
Qed.

Fixpoint finitary_seq_quot_ind
         {B : Type}{R : Eqv B}
         (P : (nat -> (B // R)) -> Prop)
         (n : nat)
         (Pn : forall f g, (forall p, p < n -> f p = g p) -> P f -> P g)
         (Pq : forall f, P (fun n => class R (f n))) f {struct n}: P f.
Proof.
  destruct n.
  - generalize (f 0).
    apply class_ind.
    intro b.
    eapply Pn.
    + intros p hp.
      exfalso.
      inversion hp.
    + unshelve apply Pq.
      intro n.
      exact b.
  -
    remember (f n) as b' eqn:eqb'.
    cut (P (fun p => if p =? n then b' else f p)) .
    + eapply Pn.
      intro p.
      case (Nat.eqb_spec); intros;congruence.
    + clear eqb'.
      revert b'.
    refine (class_ind _ _).
    intro b.
    pattern f.
    revert f.
    eapply (finitary_seq_quot_ind B R _ n).
    * intros f g  Pfg hf.
      unshelve eapply (Pn _ _ _ hf).
      cbn.
      intros p hp.
      case (Nat.eqb_spec).
      -- reflexivity.
      -- intro.
         apply Pfg.
         inversion hp; auto.
         contradiction.
    * intro f.
      cut (P (fun p => class R (if p =? n then b else f p))).
      -- eapply Pn.
         intro.
         case (Nat.eqb_spec); reflexivity.
      -- apply Pq.
Qed.
