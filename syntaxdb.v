(**
Contents
- Binding signatures with associated sytnax
- Derivation of assignments
- Models of a signature and their morphisms
- Syntax as a model
- Initiality
*)

Require Import Arith.
Require Import Basics.
Require Import micromega.Lia.

Open Scope program_scope.
Open Scope list_scope.

Require Import Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* substitution in a model *)
Reserved Notation "x [ s ]" (at level 30).
(* substitution in the syntax *)
Reserved Notation "x [ s ]ₛ" (at level 30).

(* Derivation of substitution *)
Reserved Notation "f ^ ( n )" (at level 30).

(** * Binding signatures with associated syntax
 *)


Record signature :=
  { O  : Type;
    ar : O -> list nat}.

Inductive Z (S : signature) : Type :=
  Var : nat -> Z S
| Op : forall (o : O S), vec (Z S) (ar o) (* this is Z^(length ar) *) -> Z S.


Arguments Op [S] o .
(** Example: the lambda-calculus *)
Inductive LC_O := App | Abs.

Definition LC_sig : signature :=
  {| O := LC_O;
     ar := fun o => match o with
                   App => 0 :: 0 :: nil
                 | Abs => 1 :: nil
                 end
  |}.


Definition LC := Z LC_sig.

Definition LC_app (a : LC)(b : LC) : LC :=
  Op (S := LC_sig) App (a :: b :: NilV)%v.
Definition LC_abs (a : LC) : LC :=
  Op (S := LC_sig) Abs (a :: NilV)%v.



(** * Definition of derivation


 *)


Definition subst_prime {X : Type}(z : X)(lift : X -> X) (f : nat -> X) : nat -> X :=
  fun n => match n with
          0 => z
        | S n => lift (f n)
        end.
(* derivation on substitution using renamings *)
Definition derivₙₛ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
  Nat.iter n (subst_prime (var 0) (ren S)) f .


(** Alternative definition (not used) *)
Fixpoint derivₙₛ_eq {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
      (ren_ext : forall f g, (forall x, f x = g x ) -> forall x, ren f x = ren g x)
      (ren_id :  forall x, ren id x = x)
      (ren_var : forall f n,  ren f (var n) = var (f n))
      (ren_ren : forall f g n,  ren f (ren g n) = ren (f ∘ g) n)
      (n : nat) (f : nat -> X) p :
      derivₙₛ var ren n f p = 
if p <? n then var p else ren (fun x => x + n) (f (p - n)).
Proof.
  unfold derivₙₛ.
  destruct n.
  - cbn.
    rewrite Nat.sub_0_r.

    symmetry.
    etransitivity;[|apply ren_id].
    apply ren_ext.
    apply Nat.add_0_r.
  - unfold subst_prime.
    destruct p.
    + reflexivity.
    + cbn -[leb].
      etransitivity.
      {
        apply( f_equal (ren S)).
        apply derivₙₛ_eq; auto.
      }
      unfold derivₙₛ.
      change (S p <? S n) with (p <? n).
      rewrite <- (commutes_if (ren S)).
      rewrite ren_var .
      rewrite ren_ren.
      unfold compose.
      destruct (p <? n); auto.
Qed.

    

(* derivation on enamings *)
Definition derivₙ (n : nat) (f : nat -> nat)  : nat -> nat := derivₙₛ (fun n => n)(fun f => f) n f.
(* derivation on substitution using substitution structure *)
Definition derivₛ {X : Type}(var : nat -> X)(subst : (nat -> X) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
  derivₙₛ var (fun f => subst (fun n => var (f n))) n f.


Fixpoint  s_deriv_deriv
       {X1 : Type}(var1 : nat -> X1)(ren1 : (nat -> nat) -> (X1 -> X1))
       {X2 : Type}(var2 : nat -> X2)(ren2 : (nat -> nat) -> (X2 -> X2))
       {X3 : Type}(var3 : nat -> X3)(ren3 : (nat -> nat) -> (X3 -> X3))
       (s : (nat -> X1) -> X2 -> X3)
       (u : X1 -> X3)
       (uvar : forall n, u (var1 n) = var3 n)
       (svar : forall f n, s f (var2 n) = u (f n))
       (sren : forall f g z,  s f (ren2 g z) = s ( fun n => f (g n)  )z )
       (rens : forall f g z,  ren3 f (s g z) = s ( fun n => ren1 f (g n)  )z )
       f g n m  
  :
    s (derivₙₛ var1 ren1 m f) (derivₙₛ var2 ren2 m g n) =
    derivₙₛ var3 ren3 m (fun n0 : nat => s f (g n0)) n.
Proof.
  destruct m as [|m].
  - reflexivity.
  - cbn.
    destruct n as [|n].
    + cbn.
      etransitivity.
      apply svar.
      apply uvar.
    + cbn.
      etransitivity.
      apply sren.
      cbn.
      etransitivity; revgoals.
      {
        apply(f_equal (ren3 S)).
        eapply (s_deriv_deriv _ _ _ _ _ _ _ _ _ s u) ; eassumption.
      }
      symmetry.
      apply rens.
Qed.


Fixpoint derivₙₛ_natural
      {X : Type} (varX : nat -> X) (renX : (nat -> nat) -> (X -> X))
      {Y : Type} (varY : nat -> Y) (renY : (nat -> nat) -> (Y -> Y))
      (g : X -> Y)(gvar : forall n, g (varX n) = varY n)
        (gren : forall f x, g (renX f x) = renY f (g x))
      (n : nat) (f : nat -> X) x :
  g (derivₙₛ varX renX n f x) = derivₙₛ varY renY n (fun n => g (f n)) x.
Proof.
  destruct n as [|n].
  - reflexivity.
  - cbn.
    destruct x; cbn.
    + apply gvar.
    + etransitivity; revgoals.
      { 
      apply(f_equal (renY S)).
      eapply (derivₙₛ_natural _ varX renX) ; eassumption.
      }
      apply gren.
Qed.

Lemma derivₙ_id  (p : nat)(n : nat)  : 
  derivₙ n (fun x => x) p = p.
  revert p.
  induction n.
  - reflexivity.
  - cbn.
    intro.
    destruct p as [|p].
    + reflexivity.
    + cbn.
      f_equal.
      apply IHn.
Qed.

Fixpoint derivₙₛ_ext_exact {X : Type}(var : nat -> X)(ren ren' : (nat -> nat) -> (X -> X))
      (ren_eq : forall f x, ren f x = ren' f x)
      (n : nat) (f g : nat -> X)
      p
      (fg_eq : p >= n ->  f (p - n) = g (p - n))
      { struct n}
  : derivₙₛ var ren n f p = derivₙₛ var ren' n g p .
Proof.
  destruct n as [|n].
  - cbn.
    rewrite <- minus_n_O in fg_eq.
    apply fg_eq.
    lia.
  - cbn.
    destruct p; cbn.
    + reflexivity.
    + etransitivity.
      apply ren_eq.
      f_equal.
      eapply (derivₙₛ_ext_exact).
      *  assumption.
      *  intros.
         apply fg_eq.
         lia.
Qed.

Lemma derivₙₛ_ext {X : Type}(var : nat -> X)(ren ren' : (nat -> nat) -> (X -> X))
      (ren_eq : forall f x, ren f x = ren' f x)
      (n : nat) (f g : nat -> X)
      p
      (fg_eq : forall q, q + n <= p -> f q = g q) 
  : derivₙₛ var ren n f p = derivₙₛ var ren' n g p .
Proof.
  apply derivₙₛ_ext_exact.
  assumption.
  intros.
  apply fg_eq.
  lia.
Qed.

Lemma var_derivₙ 
      {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
      (eq_ren : forall f n, ren f (var n) = var (f n))
      (n : nat) (f : nat -> nat) (x : nat) :
  var ((derivₙ n f) x) = derivₙₛ var ren n (fun p => var (f p)) x.
Proof.
  apply derivₙₛ_natural; auto.
Qed.

Lemma derivₙₛ_var {X : Type}(var : nat -> X)ren
      (eq_ren : forall f n, ren f (var n) = var (f n))
      n m : derivₙₛ var ren n var m = var m.
Proof.
    unshelve erewrite <- (var_derivₙ _ _ (fun n => n)).
    + auto.
    + cbn.
      f_equal.
      apply derivₙ_id.
Qed.

Lemma  subst_derivₙₛ
       {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
       (s : (nat -> X) -> (X -> X))
       (* (uvar : forall f n, s f (var n) = var' n) *)
       (svar : forall f n, s f (var n) = f n)
       (sren : forall f g z,  s f (ren g z) = s ( fun n => f (g n)  )z )
       (rens : forall f g z,  ren f (s g z) = s ( fun n => ren f (g n)  )z )
       (* (sext : forall f g, (forall n, f n = g n) -> forall x, s f x = s g x) *)
       (n m : nat)
       (f : nat -> X) (g : nat -> X)   :
  (s (derivₙₛ var ren m f) (derivₙₛ var ren m g n)) =
  (derivₙₛ var ren m (fun n0 : nat => s f (g n0)) n).
Proof.
  apply (s_deriv_deriv (u := id)); auto.
Qed.
Lemma derivₙₛ_derivₙ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n m : nat) (f : nat -> X)
      (g : nat -> nat) :
  derivₙₛ var ren n f (derivₙ n g m) = derivₙₛ var ren n (fun n0 : nat => f (g n0)) m.
Proof.
  apply (s_deriv_deriv (s := id)(u := id)); auto.
Qed.

Lemma ren_derivₙ_derivₙₛ 
      {X : Type}
      (var : nat -> X)
      (ren : (nat -> nat) -> (X -> X))(m n : nat) (f : nat -> X)(g : nat -> nat)
      (eq_ren : forall f n, ren f (var n) = var (f n)) 
      (ren_ren : forall f g x, ren f (ren g x) = ren (fun n => f (g n)) x)  :
      (* (ren_ext : forall f g , (forall x, f x = g x) -> forall x, ren f x = ren g x) : *)
  ren (derivₙ n g) (derivₙₛ var ren n f m) = derivₙₛ var ren n (fun n0 : nat => ren g (f n0)) m.
  Proof.
    eapply (s_deriv_deriv ); auto.
  Qed.
  

Lemma derivₛ_eq {X : Type}(var : nat -> X)
      (ren : (nat -> nat) -> (X -> X))
      (s : (nat -> X) -> (X -> X))
      (ren_eq : forall f x, ren f x = s (var ∘ f) x)
      (n : nat) (f : nat -> X)
      p
  : derivₛ var s n f p = derivₙₛ var ren n f p .
Proof.
  apply derivₙₛ_ext.
  - symmetry; apply ren_eq.
  - reflexivity.
Qed.






(** * Models of a signature and their morphisms *)

Section binding_condition.

  Context
    {X : Type}
    (var : nat -> X)
    (s : (nat -> X) -> X -> X).

  (* Notations (local to this section) *)
  Notation "x [ f ]" := (s f x).
  Notation "f ^ ( n )" := (derivₛ var s n f).

  Definition binding_condition
           (a : list nat) (op : vec X a -> X) :=
  forall (f : nat -> X)(v : vec X a),
    op v [ f ] = op (vec_map (fun n x => x [ f ^ ( n )]) v).

End binding_condition.

Record model_data (S : signature) := 
  { carrier :> Type;
    variables : nat -> carrier;
    ops : forall (o : O S), vec carrier (ar o) -> carrier;
    substitution : (nat -> carrier) -> (carrier -> carrier)
  }.

Arguments ops [S m] o.
Notation "x [ s ]" := (substitution s x).
Notation "f ^ ( n )" := (derivₛ (variables _) (substitution (m := _)) n f) .

(* In every model of lambda calculus, we have an app and abs operation *)
Definition app (m : model_data LC_sig) (a : m)(b : m) : m :=
  ops (S := LC_sig) App (a :: b :: NilV)%v.
Definition abs (m : model_data LC_sig)(a : m) : m :=
  ops (S := LC_sig) Abs (a :: NilV)%v.

Record is_model {S : signature}(m : model_data S) :=
  {
    (* fun ext for substitution *)
    substitution_ext : forall (f g : nat -> m),  (forall n, f n = g n) -> forall x,
                                    x [ f ] = x [ g ] ;
    variables_subst : forall x f, (variables m x) [ f ] = f x;
    (* operations are module morphisms *)
    ops_subst : 
      forall (o : O S), binding_condition (variables m) (substitution (m := m))
                                     (ops o)
              ;
    (* additionnal laws (not needed for initiality) : associativity of substitution *) 
    assoc : forall (f g : nat -> m) (x : m),
        x [ g ] [ f ] = x [ (fun n => (g n) [ f ]) ] ;

    id_neutral : forall (x : m), x [ variables m ] = x
  }.



Record model (S : signature) :=
  { mod_carrier :> model_data S;
    mod_laws : is_model mod_carrier
  }.

(** not used *)
Lemma derivₙₛ_in_model {S}{X : model S}(f : nat -> X) n p :
      f ^(n) p = if p <? n then variables X p else f (p - n) [fun x => variables X (x + n)] .

Proof.
  apply derivₙₛ_eq.
  - intros.
    apply substitution_ext; [apply mod_laws|].
    auto.
  - intros.
    apply id_neutral ; apply mod_laws.
  - intros.
    cbn.
    refine (variables_subst (mod_laws X) _ _).
  - intros.
    etransitivity.
    apply assoc ; apply mod_laws.
    apply substitution_ext; [apply mod_laws|].
    intro.
    refine (variables_subst (mod_laws X) _ _).
Qed.

Record is_model_mor
       {S : signature} (X : model_data S) (Y : model_data S)
       (u : X -> Y) :=
  {
    variables_mor : forall n, u (variables X n) = variables Y n ;
    substitution_mor : forall (f : nat -> X) (x : X), u (x [ f ]) =
                                              (u x) [ u ∘ f ];
    ops_mor : forall (o : O S)(v : vec X (ar o)), u (ops o v) =
                                             ops o (vec_map (fun _ => u) v)
  }.

Record model_mor {S : signature} (X : model_data S) (Y : model_data S) :=
  { mor_carrier :> X -> Y ;
    mor_laws : is_model_mor mor_carrier
  }.

(* model morphisms compose *)
Lemma is_model_mor_compose 
       {S : signature} (X : model_data S) (Y Z : model_data S)
       (u : X -> Y)(v : Y -> Z)
       (um : is_model_mor u)(vm : is_model_mor v) :
  is_model_mor (v ∘ u).
Proof.
  unfold compose.
  split; cbn; intros.
  - rewrite 2 variables_mor; auto.
  - rewrite 2 substitution_mor; auto.
  - rewrite 2 ops_mor; auto.
    f_equal.
    apply vec_map_map.
Qed.


(** * Syntax as a model *)

(** Renaming *)
Fixpoint Z_ren {S : signature}  (f : nat -> nat) (x : Z S) {struct x} : Z S :=
  match x with
    Var _ n => Var _ (f n)
  | Op op  v => Op op (vec_map (fun n b => (Z_ren (derivₙ n f) b))  v)
  end.



(** Substitution *)
Fixpoint Z_subst {S : signature}  (f : nat -> Z S) (x : Z S) : Z S :=
  match x with
    Var _ n => f n
  | Op op v => Op op
                 (vec_map 
                    (fun n b =>
                       (b [ derivₙₛ (Var S) Z_ren n f ]ₛ)
                    ) v)
  end
    where "t [ f ]ₛ" := (Z_subst f t).

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
    apply vec_map_ext.
    intros.
    apply Z_subst_ext.
    intro.
    eapply derivₙₛ_ext.
    + reflexivity.
    + intros; apply eq.
Defined.

Fixpoint Z_ren_subst_eq {S} (f : nat -> nat) (x : Z S) :
  Z_ren f x = x [ fun n => Var S (f n) ]ₛ.
Proof.
  destruct x.
  - reflexivity.
  - cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    rewrite Z_ren_subst_eq.
    cbn.
    apply Z_subst_ext.
    intro.
    apply var_derivₙ.
    reflexivity.
Qed.


(* Uniqueness of the renamings *)
Fixpoint ZModel_unique_ren (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_var : forall (f : nat -> Z S) n, s f (Var S n) = f n)
      (s_ops : forall (o : O S), binding_condition (Var S) s (Op o))
      (s_ext : forall (f g : nat -> Z S), (forall n, f n = g n) -> forall x, s f x = s g x)
      f z {struct z} :
    s (fun n => Var S (f n)) z = Z_ren f z.
Proof.
  intros.
  destruct z.
  - apply s_var.
  - etransitivity.
    apply s_ops.
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    etransitivity ; revgoals.
    apply (ZModel_unique_ren S s s_var s_ops s_ext) .
    apply s_ext.
    intro n.
    cbn.
    symmetry.
    apply var_derivₙ.
    intros.
    refine (s_var _ _).
Qed.

(* Uniqueness of the substitution *)
Fixpoint ZModel_unique_subst (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_var : forall (f : nat -> Z S) n, s f (Var S n) = f n)
      (s_ops : forall (o : O S), binding_condition (Var S) s (Op o))
      (s_ext : forall (f g : nat -> Z S), (forall n, f n = g n) -> forall x, s f x = s g x)
       f z {struct z} :
    s f z = z [ f ]ₛ. 
Proof.
  intros.
  destruct z.
  - apply s_var.
  - etransitivity.
    apply s_ops.
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    etransitivity.
    apply (ZModel_unique_subst _ _ s_var s_ops s_ext).
    apply Z_subst_ext.
    intro n.
    apply derivₙₛ_ext.
    + apply (ZModel_unique_ren s_var s_ops s_ext).
    + reflexivity.
Qed.

Fixpoint Z_ren_subst {S : signature} g f (z : Z S) :
Z_ren g z [ f ]ₛ = z [ fun n => f (g n)  ]ₛ.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_ext.
    intros.
    cbn.
    etransitivity;[apply Z_ren_subst|].
    apply Z_subst_ext.
    intro n.
    apply derivₙₛ_derivₙ.
Qed.

Lemma Z_ren_ren {S : signature} g f (z : Z S) :
Z_ren g (Z_ren f z) = Z_ren (g ∘ f) z.
  rewrite Z_ren_subst_eq at 1.
  rewrite Z_ren_subst.
  symmetry.
  apply Z_ren_subst_eq.
Qed.


Fixpoint Z_subst_ren {S : signature} g f (z : Z S) :
Z_ren g (z [ f ]ₛ) = z [ fun n => Z_ren g (f n)  ]ₛ.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_ext.
    intros.
    cbn.
    etransitivity;[apply Z_subst_ren|].
    apply Z_subst_ext.
    intro n.
    apply ren_derivₙ_derivₙₛ.
    + reflexivity.
    + intros. apply Z_ren_ren.
Qed.

Fixpoint Z_subst_subst {S : signature}
      (f g : nat -> Z S) (x : Z S) :
  (x [g]ₛ) [f]ₛ = x [fun n : nat => g n [f]ₛ]ₛ.
Proof.
  destruct x.
  - reflexivity.
  - cbn.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_ext.
    intros.
    cbn.
    etransitivity;[apply Z_subst_subst|].
    apply Z_subst_ext.
    intro n.
    cbn.
    (* ca devrait marcher *)
    apply subst_derivₙₛ.
    + reflexivity.
    + intros. apply Z_ren_subst.
    + intros. apply Z_subst_ren.
Qed.


Fixpoint Z_subst_id {S} (z : Z S) : z [Var S ]ₛ = z.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    etransitivity;[|apply vec_map_id].
    apply vec_map_ext.
    intros.
    etransitivity;[|apply Z_subst_id].
    apply Z_subst_ext.
    intro n.
    apply derivₙₛ_var.
    reflexivity.
Qed.
  

Lemma Z_model_laws (S : signature) : is_model (Z_model_data S).
Proof.
  repeat split.
  - exact Z_subst_ext.
  - intros o v f.
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    apply Z_subst_ext.
    intro.
    symmetry.
    apply derivₛ_eq.
    intros.
    rewrite Z_ren_subst_eq.
    reflexivity.
  - apply Z_subst_subst. 
  - apply Z_subst_id.
Qed.


Definition ZModel (S : signature) : model S :=
  {| mod_carrier := Z_model_data S; mod_laws := Z_model_laws S |}.

(** * Initial morphism from the syntax *)

Fixpoint ini_mor {S : signature} (m : model_data S )(x : Z S) : m :=
  match x with
        Var _ n => variables _ n
      | Op o v   => ops o (vec_map (fun _ => ini_mor m) v)
  end.

(* the initial morphism preserves renaming *)
Fixpoint ini_mor_ren { S : signature}(m : model S)(f : nat -> nat) (x : Z S) :
  ini_mor m (Z_ren f x) = (ini_mor m x) [ variables m ∘ f ].
  destruct x as [n|o v].
  - cbn.
    rewrite (variables_subst (mod_laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_subst (mod_laws m)).
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * cbn -[leb].
        rewrite ini_mor_ren.
        cbn -[leb].
        apply (substitution_ext (mod_laws m)).
        intro n.
        unfold compose.
        apply var_derivₙ.
        cbn.
        intros.
        rewrite (variables_subst (mod_laws m)).
        reflexivity.
Defined.


(* the initial morphism preserves substitution *)
Fixpoint ini_mor_subst {S : signature}(m : model S)(f : nat -> Z S) (x : Z S) :
  (* ini_mor m (x [ f ]ₛ) = (ini_mor m x) [fun y => ini_mor m (f y)]. *)
  ini_mor m (x [ f ]ₛ) = (ini_mor m x) [ ini_mor m ∘ f].
  destruct x as [n|o v].
  - cbn.
    rewrite (variables_subst (mod_laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_subst (mod_laws m)).
    repeat rewrite vec_map_map.
    cbn -[leb].
    apply f_equal.
    induction v.
    + reflexivity.
    + cbn -[leb].
      f_equal; revgoals.
      * exact IHv.
      * rewrite ini_mor_subst.
        apply (substitution_ext (mod_laws m)).
        intro n.
        unfold compose.
        apply derivₙₛ_natural.
        -- reflexivity.
        -- intros.
           apply ini_mor_ren.
Qed.


Lemma ini_mor_is_model_mor {S : signature}(m : model S) : is_model_mor (X := ZModel S) (ini_mor m).
Proof.
  split; auto.
  apply ini_mor_subst.
Qed.

Program Definition initial_morphism {S : signature}(m : model S) : model_mor (ZModel S) m :=
  {|
  mor_carrier := ini_mor m;
  mor_laws := ini_mor_is_model_mor m
  |}.

Fixpoint initial_morphism_unique {S : signature}(m : model_data S)
         (f : (ZModel S) -> m) (hf : is_model_mor f)
     x : f x = ini_mor m x. 
Proof.
  destruct x.
  - apply (variables_mor hf ).
  - etransitivity.
    apply (ops_mor hf).
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    apply initial_morphism_unique.
    assumption.
Qed.


Corollary initial_morphism_unique' {S : signature}(m : model_data S)
         (f : model_mor (ZModel S) m) 
         x : f x = ini_mor m x .
  exact (initial_morphism_unique f.(mor_laws) x).
Qed.
