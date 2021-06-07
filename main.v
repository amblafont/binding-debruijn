Require Import Arith.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* on pourrait aussi faire { A : Type & A -> list nat}, comme def de signature *)
Definition sig := list nat -> Type.

Definition sig_LC : sig :=
  fun l => match l with
             1 :: nil | 0 :: 0 :: nil => unit
           | _ => False
           end.

(* Vec A B l, c'est une liste d'elements de A de meme taille que l *)
Inductive Vec {A : Type} (B : Type) : list A -> Type :=
    NilV : Vec B nil
  | ConsV : forall a lA, B -> Vec B lA -> Vec B (a :: lA).



Inductive Z (Sig : sig) : Type :=
  Var : nat -> Z Sig
| Op : forall ar, Sig ar -> Vec (Z Sig) ar (* en gros, c'est Z^(length ar) *) -> Z Sig.


Definition Vec_map {A B C : Type}(f : A -> B -> C) :=
  fix rec (l : list A) (v : Vec B l) : Vec C l :=
  match v with
    NilV _ => NilV _
  | ConsV a b lB => ConsV a (f a b) (rec _ lB)
    end.

Lemma vec_map_map {A B C D : Type}(f : A -> B -> C) (g : A -> C -> D) {l : list A}
      (v : Vec B l) : Vec_map g (Vec_map f v) = Vec_map (fun a b => g a (f a b)) v.
  induction v; cbn; congruence.
Qed.

Lemma vec_map_fun_ext {A B C : Type}(f g : A -> B -> C) {l : list A}
      (v : Vec B l) (h : forall a b, f a b = g a b): Vec_map f v = Vec_map g v.
  induction v; cbn; congruence.
Qed.



Fixpoint Z_ren {Sig : sig}  (f : nat -> nat) (x : Z Sig) {struct x} : Z Sig :=
  match x with
    Var _ n => Var _ (f n)
  | @Op _ ar op v => Op op (Vec_map (fun n b => (Z_ren (fun p => if p <? n then p else f (p - n) + n) b))  v)
  end.

Fixpoint Z_subst {Sig : sig}  (f : nat -> Z Sig) (x : Z Sig) : Z Sig :=
  match x with
    Var _ n => f n
  | @Op _ ar op v => Op op
                        (Vec_map 
                           (fun n b => (Z_subst (fun p => if p <? n then Var Sig p else Z_ren (fun x => x + n) (f (p - n))) b)
                        ) v)
    end.


Record model (Sig : sig) :=
  { carrier :> Type;
    variables : nat -> carrier;
    substitution : (nat -> carrier) -> carrier -> carrier ;
    ops : forall (ar : list nat), Sig ar -> Vec carrier ar ->
                                             carrier;
    (* fun ext pour la substitution *)
    substitution_ext : forall f g x,  (forall n, f n = g n) -> 
                                    substitution f x = substitution g x;
    variables_eq : forall x f, substitution f (variables x) = f x;
    (* les operations sont des morphismes de module *)
    ops_eq : forall (ar : list nat)
                    (o : Sig ar)
                    (v : Vec carrier ar)
                    (f : nat -> carrier),
          substitution f (ops o v) =
          @ops  ar o (Vec_map
                        (fun n =>
                           substitution
                             (fun x => if x <? n then variables x else
                                         substitution (fun p => variables (p + n)) (f (x - n)))) v)
                     
  }.


Fixpoint ini_mor {Sig : sig} (m : model Sig )(x : Z Sig) : m :=
  match x with
        Var _ n => variables _ n
      | @Op _ ar op v   => ops op (Vec_map (fun _ => ini_mor m) v)
  end.

(* le morphisme initial preserve le renommage *)
Fixpoint mor_ren { Sig : sig}(m : model Sig)(f : nat -> nat) (x : Z Sig) :
  ini_mor m (Z_ren f x) = substitution (fun y => variables _ (f y)) (ini_mor m x).
  destruct x as [n|ar o v].
  - cbn.
    rewrite variables_eq.
    reflexivity.
  - cbn -[leb].
    rewrite ops_eq.
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    clear o.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * cbn -[leb].
        rewrite mor_ren.
        cbn -[leb].
        apply substitution_ext.
        intro n.
        destruct (n <? a).
        --  reflexivity.
        --  rewrite variables_eq.
            reflexivity.
Defined.


(* le morphisme initial preserve la substitution *)
Fixpoint mor_subst { Sig : sig}(m : model Sig)(f : nat -> Z Sig) (x : Z Sig) :
  ini_mor m (Z_subst f x) = substitution (fun y => ini_mor m (f y)) (ini_mor m x).
  destruct x as [n|ar o v].
  - cbn.
    rewrite variables_eq.
    reflexivity.
  - cbn -[leb].
    rewrite ops_eq.
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    clear o.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * cbn -[leb].
        rewrite mor_subst.
        cbn -[leb].
        apply substitution_ext.
        intro n.
        destruct (n <? a).
        --  reflexivity.
        --  apply mor_ren.
Defined.
