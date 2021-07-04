(** vectors and various lemmas *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* vec {A} B l is a B-list of the same size as l *)
Inductive vec {A : Type} (B : Type) : list A -> Type :=
    NilV : vec B nil
  | ConsV : forall a lA, B -> vec B lA -> vec B (a :: lA).

Arguments NilV {A}{B}.

Definition vec_hd {A B}(a : A)(l : list A)(v : vec B (a :: l)) : B :=
  match v with ConsV _ b _ => b end.
Definition vec_tl {A B}(a : A)(l : list A)(v : vec B (a :: l)) : vec B l :=
  match v with ConsV _ _ v => v end.

  
Declare Scope vec_scope.
Delimit Scope vec_scope with v.

Infix "::" := (ConsV _) (only parsing) : vec_scope.

Definition vec_map {A B C : Type}(f : A -> B -> C) :=
  fix rec (l : list A) (v : vec B l) : vec C l :=
  match v with
    NilV => NilV
  | ConsV a b lB => ConsV a (f a b) (rec _ lB)
    end.

Definition vec_hd_map  {A B C}(a : A)(l : list A)(f : A -> B -> C)
                          (v : vec B (a :: l)) :
                         vec_hd (vec_map f v) = f a (vec_hd v) :=
  match v with ConsV _ b v' => eq_refl _ end.

Definition vec_tl_map  {A B C}(a : A)(l : list A)(f : A -> B -> C)
                          (v : vec B (a :: l)) :
                         vec_tl (vec_map f v) = vec_map f (vec_tl v) :=
  match v with ConsV _ b v' => eq_refl _ end.

Fixpoint vec_map_id {A B : Type}{l : list A}(v : vec B l) : vec_map (fun _ x => x) v = v.
  destruct v.
  -  reflexivity.
  -  cbn.
     f_equal.
     apply vec_map_id.
Defined.

Lemma vec_map_map {A B C D : Type}(f : A -> B -> C) (g : A -> C -> D) {l : list A}
      (v : vec B l) : vec_map g (vec_map f v) = vec_map (fun a b => g a (f a b)) v.
  induction v; cbn; congruence.
Qed.

Definition vec_map_ext {A B C : Type}(f g : A -> B -> C) {l : list A}
      (v : vec B l) (h : forall a b, f a b = g a b): vec_map f v = vec_map g v.
  induction v; cbn; congruence.
Defined.

Fixpoint vec_max {A : Type}(l : list A) (v : vec nat l) : nat :=
  match v with
    NilV => 0
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
