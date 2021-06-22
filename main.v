Require Import Arith.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Signatures could alternatively be defined as { A : Type & A -> list nat} *)
Record sig :=  { O : Type;
                 ar : O -> list nat}.

Inductive O_LC :=
  App | Abs.
Definition sig_LC : sig :=
  {| O := O_LC;
     ar := fun o => match o with
                   App => 0 :: 0 :: nil
                 | Abs => 1 :: nil
                 end

  |}.

(* Vec {A} B l is a B-list of the same size as l *)
Inductive Vec {A : Type} (B : Type) : list A -> Type :=
    NilV : Vec B nil
  | ConsV : forall a lA, B -> Vec B lA -> Vec B (a :: lA).


Inductive Z (Sig : sig) : Type :=
  Var : nat -> Z Sig
| Op : forall (o : O Sig), Vec (Z Sig) (ar o) (* this is Z^(length ar) *) -> Z Sig.

Arguments Op [Sig] o.

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

Definition vec_map_fun_ext {A B C : Type}(f g : A -> B -> C) {l : list A}
      (v : Vec B l) (h : forall a b, f a b = g a b): Vec_map f v = Vec_map g v.
  induction v; cbn; congruence.
Defined.



Fixpoint Z_ren {Sig : sig}  (f : nat -> nat) (x : Z Sig) {struct x} : Z Sig :=
  match x with
    Var _ n => Var _ (f n)
  | Op op  v => Op op (Vec_map (fun n b => (Z_ren (fun p => if p <? n then p else f (p - n) + n) b))  v)
  end.

Fixpoint Z_subst {Sig : sig}  (f : nat -> Z Sig) (x : Z Sig) : Z Sig :=
  match x with
    Var _ n => f n
  | Op op v => Op op
                        (Vec_map 
                           (fun n b => (Z_subst (fun p => if p <? n then Var Sig p else Z_ren (fun x => x + n) (f (p - n))) b)
                        ) v)
    end.


Record model_data (Sig : sig) := 
  { carrier :> Type;
    variables : nat -> carrier;
    ops : forall (o : O Sig), Vec carrier (ar o) -> carrier;
    substitution : (nat -> carrier) -> carrier -> carrier ;
  }.
Arguments ops [Sig m] o.

Record model_laws {Sig : sig}(m : model_data Sig) :=
  {
    (* fun ext for substitution *)
    substitution_ext : forall (f g : nat -> m),  (forall n, f n = g n) -> forall x,
                                    substitution f x = substitution g x;
    variables_eq : forall x f, substitution f (variables m x) = f x;
    (* operations are module morphisms *)
    ops_eq : forall (o : O Sig)
               (v : Vec m (ar o))
               (f : nat -> m),
          substitution f (ops o v) =
          ops o (Vec_map
                        (fun n =>
                           substitution
                             (fun x => if x <? n then variables m x else
                                         substitution (fun p => variables m (p + n)) (f (x - n)))) v)
    (* missing laws: associativity of substitution *) ;
    assoc : forall (f g : nat -> m) (x : m),
        substitution f (substitution g x) = substitution (fun n => substitution f (g n)) x ;
    id_neutral : forall (x : m), substitution (variables m) x = x
  }.

Record model (Sig : sig) :=
  { data :> model_data Sig;
    laws : model_laws data
  }.

Record model_mor {Sig : sig} (X : model Sig) (Y : model Sig) :=
  { carrier_mor :> X -> Y ;
    variables_mor : forall n, carrier_mor (variables X n) = variables Y n ;
    substitution_mor : forall (f : nat -> X) (x : X), carrier_mor (substitution f x) =
                                              substitution (fun n => carrier_mor (f n))
                                                           (carrier_mor x) ;
    ops_mor : forall (o : O Sig)(v : Vec X (ar o)), carrier_mor (ops o v) =
                                                         ops o (Vec_map (fun _ => carrier_mor) v)
  
  }.

(* Z is a model *)


Fixpoint Z_subst_funext {Sig}(f g : nat -> Z Sig) (eq : forall n, f n = g n) x :
  Z_subst f x = Z_subst g x.
Proof.
  destruct x.
  - cbn; apply eq.
  - cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply Z_subst_funext.
    intro.
    rewrite eq.
    reflexivity.
Qed.

Fixpoint Z_ren_subst_eq {Sig} (f : nat -> nat) (x : Z Sig) :
  Z_ren f x = Z_subst (fun n => Var Sig (f n)) x.
Proof.
  destruct x.
  - reflexivity.
  - cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    rewrite Z_ren_subst_eq.
    cbn.
    apply Z_subst_funext.
    intro.
    destruct a; [reflexivity|].
    destruct (n <=? a); reflexivity.
Qed.
          
Definition Z_model_data (Sig : sig) : model_data Sig :=
  {|
  carrier := Z Sig;
  variables := Var Sig;
  ops := @Op Sig;
  substitution := Z_subst
 |}.


Lemma commutes_if {A B : Type}(f : A -> B)(b : bool) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
destruct b; reflexivity.
Qed.

(* Uniqueness of the renamings *)
Fixpoint ZModel_unique_ren (Sig : sig) (s : (nat -> Z Sig) -> Z Sig -> Z Sig)
      (s_laws : model_laws {| carrier := Z Sig;
                              variables := Var Sig;
                              ops := @Op Sig;
                              substitution := s|}) f z {struct z} :
    s (fun n => Var Sig (f n)) z = Z_ren f z.
Proof.
  intros.
  destruct z.
  - apply (variables_eq s_laws).
  - etransitivity.
    apply (ops_eq s_laws).
    cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    etransitivity. 
    {  apply (substitution_ext s_laws).
       intro n.
       rewrite (variables_eq s_laws (f (n - a))). 
       apply (commutes_if (Var Sig)).
    }
    apply (ZModel_unique_ren _ _ s_laws).
Qed.

(* Uniqueness of the substitution *)
Fixpoint ZModel_unique_subst (Sig : sig) (s : (nat -> Z Sig) -> Z Sig -> Z Sig)
      (s_laws : model_laws {| carrier := Z Sig;
                              variables := Var Sig;
                              ops := @Op Sig;
                              substitution := s|}) f z {struct z} :
    s f z = Z_subst f z.
Proof.
  intros.
  destruct z.
  - apply (variables_eq s_laws).
  - etransitivity.
    apply (ops_eq s_laws).
    cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    etransitivity.
    apply (ZModel_unique_subst _ _ s_laws).
    apply Z_subst_funext.
    intro n.
    rewrite (ZModel_unique_ren s_laws).
    reflexivity.
Qed.


Lemma Z_model_laws (Sig : sig) : model_laws (Z_model_data Sig).
Proof.
  repeat split.
  - exact Z_subst_funext.
  - cbn.
    intros o v f.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply Z_subst_funext.
    intro.
    rewrite Z_ren_subst_eq.
    reflexivity.
  - admit.
  - admit.

Admitted.

Definition ZModel (Sig : sig) : model Sig :=
  {| data := Z_model_data Sig; laws := Z_model_laws Sig |}.

(* the initial morphism *)

Fixpoint ini_mor {Sig : sig} (m : model Sig )(x : Z Sig) : m :=
  match x with
        Var _ n => variables _ n
      | Op o v   => ops o (Vec_map (fun _ => ini_mor m) v)
  end.

(* the initial morphism preserves renaming *)
Fixpoint mor_ren { Sig : sig}(m : model Sig)(f : nat -> nat) (x : Z Sig) :
  ini_mor m (Z_ren f x) = substitution (fun y => variables _ (f y)) (ini_mor m x).
  destruct x as [n|o v].
  - cbn.
    rewrite (variables_eq (laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_eq (laws m)).
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * cbn -[leb].
        rewrite mor_ren.
        cbn -[leb].
        apply (substitution_ext (laws m)).
        intro n.
        destruct (n <? a).
        --  reflexivity.
        --  rewrite (variables_eq (laws m)).
            reflexivity.
Defined.


(* the initial morphism preserves substitution *)
Fixpoint mor_subst {Sig : sig}(m : model Sig)(f : nat -> Z Sig) (x : Z Sig) :
  ini_mor m (Z_subst f x) = substitution (fun y => ini_mor m (f y)) (ini_mor m x).
  destruct x as [n|o v].
  - cbn.
    rewrite (variables_eq (laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_eq (laws m)).
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * cbn -[leb].
        rewrite mor_subst.
        cbn -[leb].
        apply (substitution_ext (laws m)).
        intro n.
        destruct (n <? a).
        --  reflexivity.
        --  apply mor_ren.
Defined.


Program Definition initial_morphism {Sig : sig}(m : model Sig) : model_mor (ZModel Sig) m :=
  {|
  carrier_mor := ini_mor m;
  |}.
Next Obligation.
  apply mor_subst.
Qed.

Fixpoint initial_morphism_unique {Sig : sig}(m : model Sig) (f : model_mor (ZModel Sig) m)
     x : f x = initial_morphism m x. 
Proof.
  destruct x.
  - apply variables_mor.
  - etransitivity.
    apply ops_mor.
    cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply initial_morphism_unique.
Qed.
