Require Import Arith.
Require Import Basics.
 (* for composition *)
Open Scope program_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Class has_substitution (X : Type) := substitution : (nat -> X) -> (X -> X). *)
(* Notation "x [ s ]" := (substitution s x) (at level 30). *)

(* substitution in a model *)
Reserved Notation "x [ s ]" (at level 30).
(* substitution in the syntax *)
Reserved Notation "x [ s ]ₛ" (at level 30).


Record signature :=
  { O  : Type;
    ar : O -> list nat}.

Inductive O_LC := App | Abs.

Definition signature_LC : signature :=
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


Inductive Z (S : signature) : Type :=
  Var : nat -> Z S
| Op : forall (o : O S), Vec (Z S) (ar o) (* this is Z^(length ar) *) -> Z S.

Arguments Op [S] o.

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


(* shifts on renamings *)
Definition shiftₙ (n : nat) (f : nat -> nat)  : nat -> nat :=
    fun p => if p <? n then p else f (p - n) + n.


(* shifts on substitution using renamings *)
Definition shiftₙₛ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
    fun p => if p <? n then var p else ren (fun x => x + n) (f (p - n)).

(* shifts on substitution using substitution structure *)
Definition shiftₛ {X : Type}(var : nat -> X)(subst : (nat -> X) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
  shiftₙₛ var (fun f => subst (fun n => var (f n))) n f.

Lemma commutes_if {A B : Type}(f : A -> B)(b : bool) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
destruct b; reflexivity.
Qed.

Lemma shiftₙₛ_natural
      {X : Type} (varX : nat -> X) (renX : (nat -> nat) -> (X -> X))
      {Y : Type} (varY : nat -> Y) (renY : (nat -> nat) -> (Y -> Y))
      (g : X -> Y)(gvar : forall n, g (varX n) = varY n)
        (gren : forall f x, g (renX f x) = renY f (g x))
      (n : nat) (f : nat -> X) x :
  g (shiftₙₛ varX renX n f x) = shiftₙₛ varY renY n (fun n => g (f n)) x.
Proof.
  unfold shiftₙ, shiftₙₛ.
  rewrite <- gvar, <- gren.
  symmetry.
  apply commutes_if.
Qed.

Lemma var_shiftₙ 
      {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
      (eq_ren : forall f n, ren f (var n) = var (f n))
      (n : nat) (f : nat -> nat) (x : nat) :
  var ((shiftₙ n f) x) = shiftₙₛ var ren n (fun p => var (f p)) x.
Proof.
  unfold shiftₙ.
  etransitivity; revgoals.
  eapply  (shiftₙₛ_natural (g := var)).
  - reflexivity.
  - symmetry.
    apply eq_ren.
  - reflexivity.
Qed.
  
Lemma shiftₙₛ_ext {X : Type}(var : nat -> X)(ren ren' : (nat -> nat) -> (X -> X))
      (ren_eq : forall f x, ren f x = ren' f x)
      (n : nat) (f g : nat -> X)
      (fg_eq : forall p, f p = g p) p : shiftₙₛ var ren n f p = 
                                   shiftₙₛ var ren' n g p .
Proof.
  unfold shiftₙₛ.
  rewrite fg_eq, ren_eq.
  reflexivity.
Qed.

(** Renaming *)
Fixpoint Z_ren {S : signature}  (f : nat -> nat) (x : Z S) {struct x} : Z S :=
  match x with
    Var _ n => Var _ (f n)
  | Op op  v => Op op (Vec_map (fun n b => (Z_ren (shiftₙ n f) b))  v)
  end.



(** Substitution *)
Fixpoint Z_subst {S : signature}  (f : nat -> Z S) (x : Z S) : Z S :=
  match x with
    Var _ n => f n
  | Op op v => Op op
                 (Vec_map 
                    (fun n b =>
                       (b [ shiftₙₛ (Var S) Z_ren n f ]ₛ)
                    ) v)
  end
    where "t [ f ]ₛ" := (Z_subst f t).

(* Instance Z_has_substitution (S : signature) : has_substitution (Z S) := Z_subst. *)


Record model_data (S : signature) := 
  { carrier :> Type;
    variables : nat -> carrier;
    ops : forall (o : O S), Vec carrier (ar o) -> carrier;
    (* has_subst :> has_substitution carrier *)
    substitution : (nat -> carrier) -> (carrier -> carrier)

  }.

Arguments ops [S m] o.
Notation "x [ s ]" := (substitution s x).
Notation "↑" := (shiftₛ (variables _) (substitution (m := _))).
(* Existing Instance has_subst . *)

Record model_laws {S : signature}(m : model_data S) :=
  {
    (* fun ext for substitution *)
    substitution_ext : forall (f g : nat -> m),  (forall n, f n = g n) -> forall x,
                                    x [ f ] = x [ g ] ;
    variables_eq : forall x f, (variables m x) [ f ] = f x;
    (* operations are module morphisms *)
    ops_eq : forall (o : O S)
               (v : Vec m (ar o))
               (f : nat -> m),
          substitution f (ops o v) =
          ops o (Vec_map
                        (fun n t =>
                           (* substitution (shiftₛ (variables m) substitution n f)) *)
                           (* substitution (shiftₛ (variables m) (substitution (m := m)) n f) *)
                           t [ ↑ n f ]
                        )
              v);

    (* additionnal laws (not needed for initiality) : associativity of substitution *) 
    assoc : forall (f g : nat -> m) (x : m),
        x [ g ] [ f ] = x [ (fun n => (g n) [ f ]) ] ;
    id_neutral : forall (x : m), x [ variables m ] = x
  }.

Record model (S : signature) :=
  { data :> model_data S;
    laws : model_laws data
  }.

Record model_mor {S : signature} (X : model S) (Y : model S) :=
  { carrier_mor :> X -> Y ;
    variables_mor : forall n, carrier_mor (variables X n) = variables Y n ;
    substitution_mor : forall (f : nat -> X) (x : X), carrier_mor (x [ f ]) =
                                              (carrier_mor x) [ carrier_mor ∘ f ];
    ops_mor : forall (o : O S)(v : Vec X (ar o)), carrier_mor (ops o v) =
                                                         ops o (Vec_map (fun _ => carrier_mor) v)
  
  }.

(* Z is a model *)

Definition Z_model_data (S : signature) : model_data S :=
  {|
  carrier := Z S;
  variables := Var S;
  ops := @Op S;
  substitution := Z_subst
 |}.

Fixpoint Z_subst_ext {S}(f g : nat -> Z S) (eq : forall n, f n = g n) x :
  x [ f ]ₛ = x [ g ]ₛ.
Proof.
  destruct x.
  - cbn; apply eq.
  - cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply Z_subst_ext.
    intro.
    eapply shiftₙₛ_ext.
    + reflexivity.
    + apply eq.
Qed.

Fixpoint Z_ren_subst_eq {S} (f : nat -> nat) (x : Z S) :
  Z_ren f x = x [ fun n => Var S (f n) ]ₛ.
Proof.
  destruct x.
  - reflexivity.
  - cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    rewrite Z_ren_subst_eq.
    cbn.
    apply Z_subst_ext.
    intro.
    apply var_shiftₙ.
    reflexivity.
Qed.


(* Uniqueness of the renamings *)
Fixpoint ZModel_unique_ren (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_laws : model_laws {| carrier := Z S;
                              variables := Var S;
                              ops := @Op S;
                              substitution := s|}) f z {struct z} :
    s (fun n => Var S (f n)) z = Z_ren f z.
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
       etransitivity;[symmetry; apply var_shiftₙ|].
       intros.
       exact (variables_eq s_laws _ _).
       reflexivity.
    }
    apply (ZModel_unique_ren _ _ s_laws).
Qed.

(* Uniqueness of the substitution *)
Fixpoint ZModel_unique_subst (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_laws : model_laws {| carrier := Z S;
                              variables := Var S;
                              ops := @Op S;
                              substitution := s|}) f z {struct z} :
    s f z = z [ f ]ₛ. 
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
    apply Z_subst_ext.
    intro n.
    apply shiftₙₛ_ext.
    + apply (ZModel_unique_ren s_laws).
    + reflexivity.
Qed.


Lemma Z_model_laws (S : signature) : model_laws (Z_model_data S).
Proof.
  repeat split.
  - exact Z_subst_ext.
  - cbn.
    intros o v f.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply Z_subst_ext.
    intro.
    unfold shiftₙₛ.
    rewrite Z_ren_subst_eq.
    reflexivity.
  - admit.
  - admit.

Admitted.

Definition ZModel (S : signature) : model S :=
  {| data := Z_model_data S; laws := Z_model_laws S |}.

(* the initial morphism *)

Fixpoint ini_mor {S : signature} (m : model S )(x : Z S) : m :=
  match x with
        Var _ n => variables _ n
      | Op o v   => ops o (Vec_map (fun _ => ini_mor m) v)
  end.

(* the initial morphism preserves renaming *)
Fixpoint mor_ren { S : signature}(m : model S)(f : nat -> nat) (x : Z S) :
  ini_mor m (Z_ren f x) = (ini_mor m x) [ variables m ∘ f ].
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
        unfold compose.
        apply var_shiftₙ.
        cbn.
        intros.
        rewrite (variables_eq (laws m)).
        reflexivity.
Defined.


(* the initial morphism preserves substitution *)
Fixpoint mor_subst {S : signature}(m : model S)(f : nat -> Z S) (x : Z S) :
  (* ini_mor m (x [ f ]ₛ) = (ini_mor m x) [fun y => ini_mor m (f y)]. *)
  ini_mor m (x [ f ]ₛ) = (ini_mor m x) [ ini_mor m ∘ f].
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
      * rewrite mor_subst.
        apply (substitution_ext (laws m)).
        intro n.
        unfold compose.
        apply shiftₙₛ_natural.
        -- reflexivity.
        -- intros.
           apply mor_ren.
Qed.



Program Definition initial_morphism {S : signature}(m : model S) : model_mor (ZModel S) m :=
  {|
  carrier_mor := ini_mor m;
  |}.
Next Obligation.
  apply mor_subst.
Qed.

Fixpoint initial_morphism_unique {S : signature}(m : model S) (f : model_mor (ZModel S) m)
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
