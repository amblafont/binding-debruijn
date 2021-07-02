
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
 (* for composition *)

Declare Scope signature_scope.

Record signature :=
  { O  : Type;
    ar : O -> list nat}.

Arguments O _%signature_scope.

Definition sum_of_signatures (S1 : signature)(S2 : signature) : signature :=
  {| O := O S1 + O S2 ;
     ar := fun o =>
             match o with
               inl o' => ar o'
               | inr o' => ar o'
               end
  |}.

Infix "+"  := sum_of_signatures : signature_scope.

Inductive O_LC := App | Abs.

Definition signature_LC : signature :=
  {| O := O_LC;
     ar := fun o => match o with
                   App => 0 :: 0 :: nil
                 | Abs => 1 :: nil
                 end
  |}.



Inductive Z (S : signature) : Type :=
  Var : nat -> Z S
| Op : forall (o : O S), Vec (Z S) (ar o) (* this is Z^(length ar) *) -> Z S.

Arguments Z S%signature_scope.
Arguments Op [S] o.




(* Link with the definition of the paper *)
Definition subst_prime {X : Type}(z : X)(lift : X -> X) (f : nat -> X) : nat -> X :=
  fun n => match n with
          0 => z
        | S n => lift (f n)
        end.
(* shifts on substitution using renamings *)
Definition shiftₙₛ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
  Nat.iter n (subst_prime (var 0) (ren S)) f .
      (* fun  p => if p <? n then var p else ren (fun x => x + n) (f (p - n)). *)


Fixpoint shiftₙₛ_eq {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
      (ren_ext : forall f g, (forall x, f x = g x ) -> forall x, ren f x = ren g x)
      (ren_id :  forall x, ren id x = x)
      (ren_var : forall f n,  ren f (var n) = var (f n))
      (ren_ren : forall f g n,  ren f (ren g n) = ren (f ∘ g) n)
      (n : nat) (f : nat -> X) p :
      shiftₙₛ var ren n f p = 
      (* Nat.iter n (subst_prime (var 0) (ren S)) f p. *)
if p <? n then var p else ren (fun x => x + n) (f (p - n)).
Proof.
  unfold shiftₙₛ.
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
        apply shiftₙₛ_eq; auto.
      }
      unfold shiftₙₛ.
      change (S p <? S n) with (p <? n).
      rewrite <- (commutes_if (ren S)).
      rewrite ren_var .
      rewrite ren_ren.
      unfold compose.
      destruct (p <? n); auto.
Qed.

    

(* shifts on renamings *)
Definition shiftₙ (n : nat) (f : nat -> nat)  : nat -> nat := shiftₙₛ (fun n => n)(fun f => f) n f.
(* shifts on substitution using substitution structure *)
Definition shiftₛ {X : Type}(var : nat -> X)(subst : (nat -> X) -> (X -> X))(n : nat) (f : nat -> X)  : nat -> X :=
  shiftₙₛ var (fun f => subst (fun n => var (f n))) n f.


Fixpoint  f_shiftₙₛ
       {X1 : Type}(var1 : nat -> X1)(ren1 : (nat -> nat) -> (X1 -> X1))
       {X2 : Type}(var2 : nat -> X2)(ren2 : (nat -> nat) -> (X2 -> X2))
       {X3 : Type}(var3 : nat -> X3)(ren3 : (nat -> nat) -> (X3 -> X3))
       (s : (nat -> X1) -> X2 -> X3)
       (u : X1 -> X3)
       (uvar : forall n, u (var1 n) = var3 n)
       (svar : forall f n, s f (var2 n) = u (f n))
       (sren : forall f g z,  s f (ren2 g z) = s ( fun n => f (g n)  )z )
       (rens : forall f g z,  ren3 f (s g z) = s ( fun n => ren1 f (g n)  )z )
       (* (sext : forall f g, (forall n, f n = g n) -> forall x, s f x = s g x) *)
       f g n m  
  :
    (s (shiftₙₛ var1 ren1 m f) (shiftₙₛ var2 ren2 m g n)) =
    (shiftₙₛ var3 ren3 m (fun n0 : nat => s f (g n0)) n).
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
        eapply (f_shiftₙₛ _ _ _ _ _ _ _ _ _ s u) ; eassumption.
      }
      symmetry.
      apply rens.
Qed.

(*
Lemma  f_shiftₙₛ
       {X1 : Type}(var1 : nat -> X1)(ren1 : (nat -> nat) -> (X1 -> X1))
       {X2 : Type}(var2 : nat -> X2)(ren2 : (nat -> nat) -> (X2 -> X2))
       {X3 : Type}(var3 : nat -> X3)(ren3 : (nat -> nat) -> (X3 -> X3))
       (s : (nat -> X1) -> X2 -> X3)
       (u : X1 -> X3)
       (uvar : forall n, u (var1 n) = var3 n)
       (svar : forall f n, s f (var2 n) = u (f n))
       (sren : forall f g z,  s f (ren2 g z) = s ( fun n => f (g n)  )z )
       (rens : forall f g z,  ren3 f (s g z) = s ( fun n => ren1 f (g n)  )z )
       (* (sext : forall f g, (forall n, f n = g n) -> forall x, s f x = s g x) *)
       f g m n
  :
    (s (shiftₙₛ var1 ren1 m f) (shiftₙₛ var2 ren2 m g n)) =
    (shiftₙₛ var3 ren3 m (fun n0 : nat => s f (g n0)) n).
  unfold shiftₙ, shiftₙₛ.
  cbn -[leb].
  rewrite <- (commutes_if (s _)).
  cbn -[leb].
  destruct (n <? m) eqn:eqna.
  + rewrite svar.
    rewrite eqna.
    apply uvar.
  + cbn -[leb].
    rewrite sren.
    erewrite sext; revgoals.
    {
      intro.
      case(Nat.ltb_spec _ _).
      + intro. exfalso. lia.
      + intros. f_equal.
        rewrite Nat.add_sub.
        reflexivity.
    }
    symmetry.
    apply rens.
Qed.
*)
Fixpoint shiftₙₛ_natural
      {X : Type} (varX : nat -> X) (renX : (nat -> nat) -> (X -> X))
      {Y : Type} (varY : nat -> Y) (renY : (nat -> nat) -> (Y -> Y))
      (g : X -> Y)(gvar : forall n, g (varX n) = varY n)
        (gren : forall f x, g (renX f x) = renY f (g x))
      (n : nat) (f : nat -> X) x :
  g (shiftₙₛ varX renX n f x) = shiftₙₛ varY renY n (fun n => g (f n)) x.
Proof.
  destruct n as [|n].
  - reflexivity.
  - cbn.
    destruct x; cbn.
    + apply gvar.
    + etransitivity; revgoals.
      { 
      apply(f_equal (renY S)).
      eapply (shiftₙₛ_natural _ varX renX) ; eassumption.
      }
      apply gren.
Qed.

Lemma shiftₙ_id  (p : nat)(n : nat)  : 
  shiftₙ n (fun x => x) p = p.
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

Fixpoint shiftₙₛ_ext {X : Type}(var : nat -> X)(ren ren' : (nat -> nat) -> (X -> X))
      (ren_eq : forall f x, ren f x = ren' f x)
      (n : nat) (f g : nat -> X)
      p
      (fg_eq : forall q, q + n <= p -> f q = g q) { struct n}
  : shiftₙₛ var ren n f p = shiftₙₛ var ren' n g p .
Proof.
  destruct n as [|n].
  - cbn.
    apply fg_eq.
    rewrite plus_n_O.
    reflexivity.
  - cbn.
    destruct p; cbn.
    + reflexivity.
    + etransitivity.
      apply ren_eq.
      f_equal.
      eapply (shiftₙₛ_ext).
      *  assumption.
      *  intros.
         apply fg_eq.
         lia.
Qed.

Lemma var_shiftₙ 
      {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
      (eq_ren : forall f n, ren f (var n) = var (f n))
      (n : nat) (f : nat -> nat) (x : nat) :
  var ((shiftₙ n f) x) = shiftₙₛ var ren n (fun p => var (f p)) x.
Proof.
  apply shiftₙₛ_natural; auto.
Qed.

Lemma shiftₙₛ_var {X : Type}(var : nat -> X)ren
      (eq_ren : forall f n, ren f (var n) = var (f n))
      n m : shiftₙₛ var ren n var m = var m.
Proof.
    unshelve erewrite <- (var_shiftₙ _ _ (fun n => n)).
    + auto.
    + cbn.
      f_equal.
      apply shiftₙ_id.
Qed.

Lemma  subst_shiftₙₛ
       {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))
       (s : (nat -> X) -> (X -> X))
       (* (uvar : forall f n, s f (var n) = var' n) *)
       (svar : forall f n, s f (var n) = f n)
       (sren : forall f g z,  s f (ren g z) = s ( fun n => f (g n)  )z )
       (rens : forall f g z,  ren f (s g z) = s ( fun n => ren f (g n)  )z )
       (* (sext : forall f g, (forall n, f n = g n) -> forall x, s f x = s g x) *)
       (n m : nat)
       (f : nat -> X) (g : nat -> X)   :
  (s (shiftₙₛ var ren m f) (shiftₙₛ var ren m g n)) =
  (shiftₙₛ var ren m (fun n0 : nat => s f (g n0)) n).
Proof.
  apply (f_shiftₙₛ (u := id)); auto.
Qed.
Lemma shiftₙₛ_shiftₙ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n m : nat) (f : nat -> X)
      (g : nat -> nat) :
  shiftₙₛ var ren n f (shiftₙ n g m) = shiftₙₛ var ren n (fun n0 : nat => f (g n0)) m.
Proof.
  apply (f_shiftₙₛ (s := id)(u := id)); auto.
Qed.

Lemma ren_shiftₙ_shiftₙₛ 
      {X : Type}
      (var : nat -> X)
      (ren : (nat -> nat) -> (X -> X))(m n : nat) (f : nat -> X)(g : nat -> nat)
      (eq_ren : forall f n, ren f (var n) = var (f n)) 
      (ren_ren : forall f g x, ren f (ren g x) = ren (fun n => f (g n)) x)  :
      (* (ren_ext : forall f g , (forall x, f x = g x) -> forall x, ren f x = ren g x) : *)
  ren (shiftₙ n g) (shiftₙₛ var ren n f m) = shiftₙₛ var ren n (fun n0 : nat => ren g (f n0)) m.
  Proof.
    eapply (f_shiftₙₛ ); auto.
  Qed.
  

Lemma shiftₛ_eq {X : Type}(var : nat -> X)
      (ren : (nat -> nat) -> (X -> X))
      (s : (nat -> X) -> (X -> X))
      (ren_eq : forall f x, ren f x = s (var ∘ f) x)
      (n : nat) (f : nat -> X)
      p
  : shiftₛ var s n f p = shiftₙₛ var ren n f p .
Proof.
  apply shiftₙₛ_ext.
  - symmetry; apply ren_eq.
  - reflexivity.
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
Notation "f ^ ( n )" := (shiftₛ (variables _) (substitution (m := _)) n f) (at level 30).

Record is_model {S : signature}(m : model_data S) :=
  {
    (* fun ext for substitution *)
    substitution_ext : forall (f g : nat -> m),  (forall n, f n = g n) -> forall x,
                                    x [ f ] = x [ g ] ;
    variables_subst : forall x f, (variables m x) [ f ] = f x;
    (* operations are module morphisms *)
    ops_subst : 
     forall (o : O S) (v : Vec m (ar o)) (f : nat -> m),
          (ops o v) [ f ] =
          ops o (Vec_map
                        (fun n t =>
                           t [ f ^ ( n ) ]
                        )
              v);
    (* additionnal laws (not needed for initiality) : associativity of substitution *) 
    assoc : forall (f g : nat -> m) (x : m),
        x [ g ] [ f ] = x [ (fun n => (g n) [ f ]) ] ;

    id_neutral : forall (x : m), x [ variables m ] = x
  }.



Record model (S : signature) :=
  { mod_carrier :> model_data S;
    mod_laws : is_model mod_carrier
  }.

Arguments model S%signature_scope.

Lemma shiftₙₛ_in_model {S}{X : model S}(f : nat -> X) n p :
      f ^(n) p = if p <? n then variables X p else f (p - n) [fun x => variables X (x + n)] .

Proof.
  apply shiftₙₛ_eq.
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
    ops_mor : forall (o : O S)(v : Vec X (ar o)), u (ops o v) =
                                             ops o (Vec_map (fun _ => u) v)
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
    apply vec_map_ext.
    intros.
    apply Z_subst_ext.
    intro.
    eapply shiftₙₛ_ext.
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
    apply var_shiftₙ.
    reflexivity.
Qed.


(* Uniqueness of the renamings *)
Fixpoint ZModel_unique_ren (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_laws : is_model {| carrier := Z S;
                              variables := Var S;
                              ops := @Op S;
                              substitution := s|}) f z {struct z} :
    s (fun n => Var S (f n)) z = Z_ren f z.
Proof.
  intros.
  destruct z.
  - apply (variables_subst s_laws).
  - etransitivity.
    apply (ops_subst s_laws).
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    etransitivity. 
    {  apply (substitution_ext s_laws).
       intro n.
       etransitivity;[symmetry; apply var_shiftₙ|].
       intros.
       exact (variables_subst s_laws _ _).
       reflexivity.
    }
    apply (ZModel_unique_ren _ _ s_laws).
Qed.

(* Uniqueness of the substitution *)
Fixpoint ZModel_unique_subst (S : signature) (s : (nat -> Z S) -> Z S -> Z S)
      (s_laws : is_model {| carrier := Z S;
                              variables := Var S;
                              ops := @Op S;
                              substitution := s|}) f z {struct z} :
    s f z = z [ f ]ₛ. 
Proof.
  intros.
  destruct z.
  - apply (variables_subst s_laws).
  - etransitivity.
    apply (ops_subst s_laws).
    cbn.
    f_equal.
    apply vec_map_ext.
    intros.
    etransitivity.
    apply (ZModel_unique_subst _ _ s_laws).
    apply Z_subst_ext.
    intro n.
    apply shiftₙₛ_ext.
    + apply (ZModel_unique_ren s_laws).
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
    apply shiftₙₛ_shiftₙ.
Qed.

Lemma Z_ren_ren {S : signature} g f (z : Z S) :
Z_ren g (Z_ren f z) = Z_ren (g ∘ f) z.
  rewrite Z_ren_subst_eq at 1.
  rewrite Z_ren_subst.
  symmetry.
  apply Z_ren_subst_eq.
Qed.


  (* Z_ren (shiftₙ a g) (shiftₙₛ (Var S) Z_ren a f n) = shiftₙₛ (Var S) Z_ren a (fun n0 : nat => Z_ren g (f n0)) n *)
(* TODO: factoriser un principe de recurrence *)
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
    apply ren_shiftₙ_shiftₙₛ.
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
    apply subst_shiftₙₛ.
    + reflexivity.
    + intros. apply Z_ren_subst.
    + intros. apply Z_subst_ren.
Qed.


Fixpoint Z_subst_id {S} (z : Z S) : z [Var S ]ₛ = z.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    etransitivity;[|apply Vec_map_id].
    apply vec_map_ext.
    intros.
    etransitivity;[|apply Z_subst_id].
    apply Z_subst_ext.
    intro n.
    apply shiftₙₛ_var.
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
    apply shiftₛ_eq.
    intros.
    rewrite Z_ren_subst_eq.
    reflexivity.
  - apply Z_subst_subst. 
  - apply Z_subst_id.
Qed.


Definition ZModel (S : signature) : model S :=
  {| mod_carrier := Z_model_data S; mod_laws := Z_model_laws S |}.

(* the initial morphism *)

Fixpoint ini_mor {S : signature} (m : model_data S )(x : Z S) : m :=
  match x with
        Var _ n => variables _ n
      | Op o v   => ops o (Vec_map (fun _ => ini_mor m) v)
  end.

(* the initial morphism preserves renaming *)
Fixpoint mor_ren { S : signature}(m : model S)(f : nat -> nat) (x : Z S) :
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
        rewrite mor_ren.
        cbn -[leb].
        apply (substitution_ext (mod_laws m)).
        intro n.
        unfold compose.
        apply var_shiftₙ.
        cbn.
        intros.
        rewrite (variables_subst (mod_laws m)).
        reflexivity.
Defined.


(* the initial morphism preserves substitution *)
Fixpoint mor_subst {S : signature}(m : model S)(f : nat -> Z S) (x : Z S) :
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
      * rewrite mor_subst.
        apply (substitution_ext (mod_laws m)).
        intro n.
        unfold compose.
        apply shiftₙₛ_natural.
        -- reflexivity.
        -- intros.
           apply mor_ren.
Qed.


Lemma ini_mor_is_model_mor {S : signature}(m : model S) : is_model_mor (X := ZModel S) (ini_mor m).
Proof.
  split; auto.
  apply mor_subst.
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
