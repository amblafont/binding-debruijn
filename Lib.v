(** vectors and various lemmas *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Vec {A} B l is a B-list of the same size as l *)
Inductive Vec {A : Type} (B : Type) : list A -> Type :=
    NilV : Vec B nil
  | ConsV : forall a lA, B -> Vec B lA -> Vec B (a :: lA).

Definition Vec_map {A B C : Type}(f : A -> B -> C) :=
  fix rec (l : list A) (v : Vec B l) : Vec C l :=
  match v with
    NilV _ => NilV _
  | ConsV a b lB => ConsV a (f a b) (rec _ lB)
    end.

Fixpoint Vec_map_id {A B : Type}{l : list A}(v : Vec B l) : Vec_map (fun _ x => x) v = v.
  destruct v.
  -  reflexivity.
  -  cbn.
     f_equal.
     apply Vec_map_id.
Defined.

Lemma vec_map_map {A B C D : Type}(f : A -> B -> C) (g : A -> C -> D) {l : list A}
      (v : Vec B l) : Vec_map g (Vec_map f v) = Vec_map (fun a b => g a (f a b)) v.
  induction v; cbn; congruence.
Qed.

Definition vec_map_ext {A B C : Type}(f g : A -> B -> C) {l : list A}
      (v : Vec B l) (h : forall a b, f a b = g a b): Vec_map f v = Vec_map g v.
  induction v; cbn; congruence.
Defined.

Fixpoint vec_max {A : Type}(l : list A) (v : Vec nat l) : nat :=
  match v with
    NilV _ => 0
  | ConsV a b lB => Nat.max b (vec_max lB)
    end.

Lemma commutes_if {A B : Type}(f : A -> B)(b : bool) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
destruct b; reflexivity.
Qed.
Lemma if_if {A : Type}(b : bool) (x y z : A) :
  (if b then if b then x else y else z) = (if b then x else z).
  destruct b ; reflexivity.
Qed.
