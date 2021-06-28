Require Import Arith.
Require Import Basics.
 (* for composition *)
Open Scope program_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* substitution in a model *)
Reserved Notation "x [ s ]" (at level 30).
(* substitution in the syntax *)
Reserved Notation "x [ s ]ₛ" (at level 30).
(* substitution in the quotiented syntax *)
Reserved Notation "x [ s ]ₘ" (at level 30).
(* mixed substitution in the syntax *)
Reserved Notation "x ⟦ s ⟧" (at level 30).

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

(* Vec {A} B l is a B-list of the same size as l *)
Inductive Vec {A : Type} (B : Type) : list A -> Type :=
    NilV : Vec B nil
  | ConsV : forall a lA, B -> Vec B lA -> Vec B (a :: lA).


Inductive Z (S : signature) : Type :=
  Var : nat -> Z S
| Op : forall (o : O S), Vec (Z S) (ar o) (* this is Z^(length ar) *) -> Z S.

Arguments Z S%signature_scope.
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

Lemma vec_map_map_swap {A B B' C C' D : Type}
      (f  : A -> B -> C ) (g  : A -> C -> D)
      (f' : A -> B -> C') (g' : A -> C' -> D)
      (fg_f'g' : forall a b, g a (f a b) = g' a (f' a b))
      {l : list A}
      (v : Vec B l) : Vec_map g (Vec_map f v) =
                       Vec_map g' (Vec_map f' v) .
Proof.
  rewrite 2 vec_map_map.
  apply vec_map_fun_ext.
  assumption.
Qed.


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
Lemma if_if {A : Type}(b : bool) (x y z : A) :
  (if b then if b then x else y else z) = (if b then x else z).
  destruct b ; reflexivity.
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

(*
Definition ops_subst_law {S : signature} (m : model_data S) : Type :=
     forall (o : O S) (v : Vec m (ar o)) (f : nat -> m),
          (ops o v) [ f ] =
          ops o (Vec_map
                        (fun n t =>
                           (* substitution (shiftₛ (variables m) substitution n f)) *)
                           (* substitution (shiftₛ (variables m) (substitution (m := m)) n f) *)
                           t [ ↑ n f ]
                        )
              v).
*)

Record model_laws {S : signature}(m : model_data S) :=
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

Arguments model S%signature_scope.

Record model_mor {S : signature} (X : model_data S) (Y : model_data S) :=
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
Defined.

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
  - apply (variables_subst s_laws).
  - etransitivity.
    apply (ops_subst s_laws).
    cbn.
    f_equal.
    apply vec_map_fun_ext.
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
      (s_laws : model_laws {| carrier := Z S;
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

Require Import micromega.Lia.
Lemma shiftₙₛ_shiftₙ {X : Type}(var : nat -> X)(ren : (nat -> nat) -> (X -> X))(n m : nat) (f : nat -> X)g :
  shiftₙₛ var ren n f (shiftₙ n g m) = shiftₙₛ var ren n (fun n0 : nat => f (g n0)) m.
Proof.
  unfold shiftₙₛ, shiftₙ.
  cbn -[leb].
  destruct (m <? n) eqn:e.
  - rewrite e.
    reflexivity.
  - case(Nat.ltb_spec _ _).
    + intro. exfalso. lia.
    + intros.
      rewrite Nat.add_sub.
      reflexivity.
Qed.

(*
Lemma shiftₙ_shiftₙ g f a n : 
  (shiftₙ a g ∘ shiftₙ a f) n = shiftₙ a (g ∘ f) n.
Proof.
  unfold compose.
  cbn.
  unfold shiftₙₛ, shiftₙ.
  destruct (n <? a) eqn:e.
  - rewrite e.
    reflexivity.
  - case(Nat.ltb_spec _ _).
    + intro. exfalso. lia.
    + intros. f_equal.
      f_equal.
      lia.
Qed.
*)
Fixpoint Z_ren_subst {S : signature} g f (z : Z S) :
Z_ren g z [ f ]ₛ = z [ fun n => f (g n)  ]ₛ.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_fun_ext.
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
    apply vec_map_fun_ext.
    intros.
    cbn.
    etransitivity;[apply Z_subst_ren|].
    apply Z_subst_ext.
    intro n.

  unfold shiftₙ, shiftₙₛ.
  cbn -[leb].
  rewrite <- (commutes_if (Z_ren _)).
  cbn -[leb].
  destruct (n <? a) eqn:eqna.
  + reflexivity.
  + cbn -[leb].
    rewrite Z_ren_ren.
    rewrite Z_ren_ren.
    rewrite 2 Z_ren_subst_eq.
    apply Z_subst_ext.
    intro m.
    unfold compose.
    cbn -[leb].
    case(Nat.ltb_spec _ _).
    * intro. exfalso. lia.
    * intros. 
      rewrite Nat.add_sub.
      reflexivity.
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
    apply vec_map_fun_ext.
    intros.
    cbn.
    etransitivity;[apply Z_subst_subst|].
    apply Z_subst_ext.
    intro n.
    cbn.
    (* ca devrait marcher *)
  unfold shiftₙ, shiftₙₛ.
  cbn -[leb].
  rewrite <- (commutes_if (Z_subst _)).
  cbn -[leb].
  rewrite if_if.
  destruct (n <? a) eqn:eqna.
  + reflexivity.
  + cbn -[leb].
    rewrite Z_ren_subst.
    erewrite Z_subst_ext; revgoals.
    {
      intro.
  - case(Nat.ltb_spec _ _).
    + intro. exfalso. lia.
    + intros. f_equal.
      rewrite Nat.add_sub.
      reflexivity.
      }
    symmetry.
    apply Z_subst_ren.
    Qed.

Fixpoint Vec_map_id {A B : Type}{l : list A}(v : Vec B l) : Vec_map (fun _ x => x) v = v.
  destruct v.
  -  reflexivity.
  -  cbn.
     f_equal.
     apply Vec_map_id.
Defined.

Lemma shiftₙ_id (n : nat) (p : nat)  : 
  shiftₙ n (fun x => x) p = p.
  unfold shiftₙ.
  case (Nat.ltb_spec).
  + reflexivity.
  + lia.
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
Fixpoint Z_subst_id {S} (z : Z S) : z [Var S ]ₛ = z.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    etransitivity;[|apply Vec_map_id].
    apply vec_map_fun_ext.
    intros.
    etransitivity;[|apply Z_subst_id].
    apply Z_subst_ext.
    intro n.
    apply shiftₙₛ_var.
    reflexivity.
Qed.
  

Lemma Z_model_laws (S : signature) : model_laws (Z_model_data S).
Proof.
  repeat split.
  - exact Z_subst_ext.
  - intros o v f.
    cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply Z_subst_ext.
    intro.
    unfold shiftₙₛ.
    rewrite Z_ren_subst_eq.
    reflexivity.
  - apply Z_subst_subst. 
  - apply Z_subst_id.
Qed.


Definition ZModel (S : signature) : model S :=
  {| data := Z_model_data S; laws := Z_model_laws S |}.

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
    rewrite (variables_subst (laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_subst (laws m)).
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
        rewrite (variables_subst (laws m)).
        reflexivity.
Defined.


(* the initial morphism preserves substitution *)
Fixpoint mor_subst {S : signature}(m : model S)(f : nat -> Z S) (x : Z S) :
  (* ini_mor m (x [ f ]ₛ) = (ini_mor m x) [fun y => ini_mor m (f y)]. *)
  ini_mor m (x [ f ]ₛ) = (ini_mor m x) [ ini_mor m ∘ f].
  destruct x as [n|o v].
  - cbn.
    rewrite (variables_subst (laws m)).
    reflexivity.
  - cbn -[leb].
    rewrite (ops_subst (laws m)).
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

Fixpoint initial_morphism_unique {S : signature}(m : model_data S) (f : model_mor (ZModel S) m)
     x : f x = ini_mor m x. 
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

Record half_equation (S1 : signature)(S2 : signature) :=
  {
    lift_ops :> forall (m : model S1), forall (o : O S2), Vec m (ar o) -> m;
    lift_ops_subst :
           forall (m : model S1) (o : O S2) (v : Vec m (ar o)) (f : nat -> m),
          (lift_ops (o := o) v) [ f ] =
          lift_ops (o := o) (Vec_map
                        (fun n t => t [ ↑ n f ])
              v) ;
    lift_ops_natural : forall (m1 m2 : model S1) (f : model_mor m1 m2)
                         (o : O S2)(v : Vec m1 (ar o)),
        lift_ops (Vec_map (fun _ => f) v)  = f (lift_ops v)
                
  }.

Arguments lift_ops [S1 S2] h [m] o.

Record equational_theory :=
  { metavariables : signature ;
    main_signature : signature ;
    left_handside : half_equation main_signature metavariables ;
    right_handside : half_equation main_signature metavariables 
  }.

Record model_equational (E : equational_theory) :=
  { main_model :> model (main_signature E) ;
    model_eq : forall o (v : Vec main_model (ar o)),
        left_handside E main_model o v = right_handside E main_model o v
  }.

(* version avec quotietns *)
Require Import Quot.

Section relvec.

  Context (A B : Type)(R : B -> B -> Prop) .
Inductive rel_vec : forall (l : list A),
    Vec B l -> Vec B l -> Prop :=
  nil_rel_vec :  rel_vec  (NilV _) (NilV _)
| cons_rel_vec : forall n l t t' v v', rel_vec (l := l)  v v' -> R t t' -> rel_vec (ConsV n t v)(ConsV n t' v').

Lemma rel_vec_rfl (rx : forall x, R x x) l (v : Vec B l) : rel_vec v v.
  induction v.
  - constructor.
  - constructor; auto.
Qed.
  End relvec.

(* class_ind : forall [X : Type] [r : Eqv X] (P : X // r -> Prop), (forall x : X, P (x / r)) -> forall x : X // r, P x *)
Fixpoint vec_quot_ind
         {A B : Type}{R : Eqv B}{l : list A}
         (P : Vec (B // R) l -> Prop)
         (Pquot : forall (v : Vec B l), P (Vec_map (fun _ => class R) v)) 
         (v : Vec (B // R) l) : P v.
Proof.
  destruct v as [|a l b v].
  - apply (Pquot (NilV _)).
  - cbn.
    revert v b.
    unshelve refine (vec_quot_ind _  _ _ _ _  _).
    +  intros v b.
       revert b v.
       unshelve refine (class_ind _ _).
       exact (fun b v => Pquot (ConsV a b v )).
Qed.

Fixpoint vec_quot_out (A B C : Type)(R : Eqv B)(l : list A)(f : Vec B l -> C)
      (compat_f : forall b b', rel_vec R b b' -> f b = f b')
      (v : Vec (B // R) l) : C.
  destruct v as [|a l b v].
  - exact (f (NilV _)).
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

Fixpoint vec_quot_out_proj (A B C : Type)(R : Eqv B)(l : list A)(f : Vec B l -> C)
      (compat_f : forall b b', rel_vec R b b' -> f b = f b')
      (v : Vec B l) :
  vec_quot_out compat_f (Vec_map (fun _ => class R) v) = f v.
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
         (Pq : forall f, P (class R ∘ f)) f {struct n}: P f.
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
         lia.
    * intro f.
      cut (P (fun p => class R (if p =? n then b else f p))).
      -- eapply Pn.
         intro.
         case (Nat.eqb_spec); reflexivity.
      -- apply Pq.
Qed.


Inductive rel_Z (E : equational_theory) : Z (main_signature E) -> Z (main_signature E) -> Prop :=
| eqE : forall o v, rel_Z (left_handside E (ZModel _) o v) (right_handside E (ZModel _) o v) 
| reflE : forall z, rel_Z z z
| symE : forall a b, rel_Z b a -> rel_Z a b
| transE : forall a b c, rel_Z a b -> rel_Z b c -> rel_Z a c
| congrE : forall (o : O (main_signature E)) (v v' : Vec _ (ar o)),
    rel_vec (@rel_Z E)  v v' -> rel_Z (Op o v) (Op o v').
(* with rel_Zv(E : equational_theory) : forall (l : list nat) , *)
(*     Vec  (Z (main_signature E)) l -> Vec  (Z (main_signature E)) l -> Prop := *)
(*   nilE :  rel_Zv  (NilV _) (NilV _) *)
(* | consE : forall n l t t' v v', rel_Zv (l := l)  v v' -> rel_Z t t' -> rel_Zv (ConsV n t v)(ConsV n t' v'). *)

                        (*
Scheme tree_forest_rec := Induction for rel_Z Sort Prop
                                    with foest_tree_rec := Induction for rel_Zv Sort Prop.

Lemma rel_Z_ind' [E : equational_theory] [P : forall z z0 : Z (main_signature E), rel_Z z z0 -> Prop]
  [P0 : forall (l : list nat) (v v0 : Vec (Z (main_signature E)) l), rel_Zv v v0 -> Prop]
(hlr : forall (o : O (metavariables E)) (v : Vec (ZModel (main_signature E)) (ar o)),
 P (left_handside E (ZModel (main_signature E)) o v) (right_handside E (ZModel (main_signature E)) o v) (eqE v)) 
(hrfl : forall z : Z (main_signature E), P z z (reflE z)) 
(hsym : forall (a b : Z (main_signature E)) (r : rel_Z b a), P b a r -> P a b (symE r)) 
(htrans : forall (a b c : Z (main_signature E)) (r : rel_Z a b),
 P a b r -> forall r0 : rel_Z b c, P b c r0 -> P a c (transE r r0)) 
(hnil : forall (o : O (main_signature E)) (v v' : Vec (Z (main_signature E)) (ar o)) (r : rel_Zv v v'),
 P0 (ar o) v v' r -> P (Op o v) (Op o v') (congrE r)) :
P0 nil (NilV (Z (main_signature E))) (NilV (Z (main_signature E))) (nilE E) ->
(forall (n : nat) (l : list nat) (t t' : Z (main_signature E)) (v v' : Vec (Z (main_signature E)) l)
   (r : rel_Zv v v'),
 P0 l v v' r -> forall r0 : rel_Z t t', P t t' r0 -> P0 (n :: l) (ConsV n t v) (ConsV n t' v') (consE n r r0)) ->
forall (z z0 : Z (main_signature E)) (r : rel_Z z z0), P z z0 r.
*)



Definition ZEr (E : equational_theory) : Eqv (Z (main_signature E)) :=
  Build_Eqv (@rel_Z E) (@reflE E) (@symE E)(@transE E) .


Definition ZE(E : equational_theory) := Z (main_signature E) // (ZEr E).

Definition  projE{E : equational_theory} (z : Z (main_signature E)) : ZE E :=
  z / ZEr E.

Definition ZE_ops (E : equational_theory) (o : O (main_signature E)) (v : Vec (ZE E) (ar o)) :
  ZE E.
  revert v.
  unshelve eapply (vec_quot_out).
  - intro v.
    apply projE.
    revert v.
    apply Op.
  - intro v.
    cbn.
    intros v' rv.
    apply class_eq.
    apply congrE.
    assumption.
Defined.

Lemma ZE_ops_projE (E : equational_theory)
       (o : O (main_signature E)) (v : Vec (Z (main_signature E)) (ar o)) :
  ZE_ops (Vec_map (fun _ => projE) v) = projE (Op o v).

Proof.
  apply vec_quot_out_proj.
Qed.

Lemma lift_ops_Z_ren {S V : signature} (h : half_equation S V)
   (f : nat -> nat) (o : O V) v :
  Z_ren f (h (ZModel S) o v) = h (ZModel S) o (Vec_map (fun n t => Z_ren (shiftₙ n f) t) v).
Proof.
  etransitivity ; [apply Z_ren_subst_eq|].
  etransitivity ; [apply (lift_ops_subst _ (m := ZModel _) )|].
  f_equal.
  apply vec_map_fun_ext.
  intros.
  symmetry.
  etransitivity ; [apply Z_ren_subst_eq|].
  apply Z_subst_ext.
  intro n.
  cbn.
  apply var_shiftₙ.
  reflexivity.
Qed.

Fixpoint Z_ren_compat {E}(f : nat -> nat)(x y : Z (main_signature E))(r :  ZEr E x y) : 
  ZEr E (Z_ren f x) (Z_ren f y).
Proof.
 destruct r. 
 - cbn.
   rewrite 2 lift_ops_Z_ren.
   constructor.
 - constructor.
 - apply symE.
   apply Z_ren_compat.
   assumption.
 - eapply transE; apply Z_ren_compat; eassumption.
 - cbn.
   apply congrE.
   induction H.
   + cbn.
     constructor.
   + cbn.
     constructor.
     * apply IHrel_vec.
     * apply Z_ren_compat.
       assumption.
Qed.

Definition ZE_ren {E : equational_theory} (f : nat -> nat) (x : ZE E) : ZE E.
  revert x .
  unshelve eapply (factor1 _ _ (Z_ren f)).
  apply Z_ren_compat.
Defined.

Lemma ZE_ren_proj{E : equational_theory} (f : nat -> nat) (z : Z (main_signature E)):
  projE (Z_ren f z) = ZE_ren f (projE z).
Proof.
  symmetry.
  apply factorize1.
Qed.

Definition VarE {E : equational_theory} (n : nat) : ZE E := Var _ n / ZEr E.

Fixpoint ZE_mixed_subst {E : equational_theory}
         (f : nat -> ZE E) (z : Z (main_signature E)) : ZE E :=
  match z with
    Var _ n => f n
  | Op op v => ZE_ops 
                 (Vec_map 
                    (fun n x =>
                       x ⟦ shiftₙₛ VarE ZE_ren n f ⟧
                    ) v)
  end where "t ⟦ s ⟧" := (ZE_mixed_subst s t).

Fixpoint ZE_mixed_subst_ext {E}(f g : nat -> ZE E) (eq : forall n, f n = g n) (x : Z _) :
  x ⟦ f ⟧ = x ⟦ g ⟧.
Proof.
  destruct x.
  - cbn; apply eq.
  - cbn.
    f_equal.
    apply vec_map_fun_ext.
    intros.
    apply ZE_mixed_subst_ext.
    intro.
    eapply shiftₙₛ_ext.
    + reflexivity.
    + apply eq.
Qed.

Fixpoint Z_subst_quot {E : equational_theory}
      (f : nat -> Z (main_signature E)) (z : Z (main_signature E)) :
  (z [ f ]ₛ) / ZEr E = z ⟦ @projE E ∘ f ⟧.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    etransitivity; [ symmetry; apply ZE_ops_projE|].
    f_equal.
    etransitivity;[apply vec_map_map|].
    cbn.
    apply vec_map_fun_ext.
    intros n z.
    etransitivity;[ apply Z_subst_quot| ].
    cbn.
    apply ZE_mixed_subst_ext.
    intro m.
    unfold compose.
    apply shiftₙₛ_natural.
    + reflexivity.
    + cbn.
      apply ZE_ren_proj.
Qed.

Fixpoint vec_max {A : Type}(l : list A) (v : Vec nat l) : nat :=
  match v with
    NilV _ => 0
  | ConsV a b lB => Nat.max b (vec_max lB)
    end.

Fixpoint max_fv {S : signature} (z : Z S) : nat :=
  match z with
    Var _ n => n
  | Op op  v => vec_max (Vec_map (fun n x => n + max_fv x) v)
  end.

Fixpoint ZE_mixed_subst_max_fv {E} (f g : nat -> ZE E)(z : Z _)
         (hfg : forall n, n <= max_fv z -> f n = g n) {struct z} :
  z ⟦ f ⟧ = z ⟦ g ⟧.
Proof.
  destruct z.
  - cbn in hfg.
    cbn.
    apply hfg.
    reflexivity.
  - cbn.
    f_equal.
    cbn in hfg.
    revert hfg.
    induction v.
    + reflexivity.
    + cbn.
      intro hfg.
      f_equal.
      * apply ZE_mixed_subst_max_fv.
        intros.
        unfold shiftₙₛ.
        case (Nat.ltb_spec).
        -- reflexivity.
        -- intros.
           f_equal.
           cbn in hfg.
           apply hfg.
           lia.
           (* apply h. *)
           (* lia. *)
      * apply IHv.
        cbn.
        intros.
        apply hfg.
        lia.
Qed.

Fixpoint ZE_mixed_subst_compat
  (E : equational_theory) 
      (f : nat -> ZE E)(z z' : Z (main_signature E))(rz :ZEr E z z'): z ⟦ f ⟧ = z' ⟦ f ⟧.
Proof.
  destruct rz.
  - cbn.
    revert f.
    refine (finitary_seq_quot_ind (n := 1 + Nat.max (max_fv(left_handside E (ZModel (main_signature E)) o v))
                                  (max_fv (right_handside E (ZModel (main_signature E)) o v))) _ _).
    + intros f g hfg.
      erewrite 2 (ZE_mixed_subst_max_fv (f := f)(g := g)).
      * tauto.
      * intros; apply hfg; lia.
      * intros; apply hfg; lia.
    + intro h.
      do 2 rewrite <- (Z_subst_quot h).
      etransitivity.
      {
        apply (f_equal projE).
        apply  (lift_ops_subst _ (m := ZModel _) v h).
      }
      etransitivity;revgoals.
      {
        symmetry.
        apply (f_equal projE).
        apply  (lift_ops_subst _ (m := ZModel _) v h).
      }
      apply class_eq.
      constructor.
  - reflexivity.
  - symmetry.
    apply ZE_mixed_subst_compat.
    assumption.
  - etransitivity; apply ZE_mixed_subst_compat; eassumption.
  - cbn.
    f_equal.
    induction H.
    + cbn.
      constructor.
    + cbn.
      f_equal.
      * apply ZE_mixed_subst_compat.
        assumption.
      * apply IHrel_vec.
Qed.
Definition ZE_subst {E : equational_theory}  (f : nat -> ZE E) (x : ZE E) : ZE E.
  revert x f.
  unshelve refine (factor _ _ _).
  - exact (fun z f => ZE_mixed_subst f z).
  - intros z z' rz.
    cbn.
    apply extensionality.
    intro f.
    apply ZE_mixed_subst_compat.
    assumption.
Defined.

Notation "x [ f ]ₘ" := (ZE_subst f x) (at level 30).

Lemma ZE_subst_proj {E : equational_theory} f z  :
  projE (E := E) z [ f ]ₘ = z ⟦ f ⟧.
Proof.
  unfold ZE_subst, projE.
  rewrite factorize.
  reflexivity.
Qed.
Lemma ZE_subst_proj_proj {E : equational_theory} f z  :
  projE (E := E) z [ projE ∘ f ]ₘ = projE (z [ f ]ₛ).
Proof.
  etransitivity; [apply ZE_subst_proj|].
  symmetry.
  apply Z_subst_quot.
Qed.

Lemma ZE_subst_ext {E}(f g : nat -> ZE E) (fg : forall n : nat, f n = g n) : forall x : ZE E, x [ f ]ₘ = x [ g ]ₘ.
Proof.
  apply class_ind.
  intro z.
  rewrite  2 (ZE_subst_proj _ z).
  apply ZE_mixed_subst_ext.
  assumption.
Qed.

Lemma ZE_ren_var {E}(f : nat -> nat) (n : nat): ZE_ren (E := E) f (VarE n) = VarE (f n).
Proof.
  unfold ZE_ren, VarE.
  rewrite factorize1.
  reflexivity.
Qed.
      
Lemma ZE_subst_var {E} x f :
  VarE (E := E) x [ f ]ₘ = f x.
Proof.
  unfold ZE_subst, VarE.
  rewrite factorize.
  reflexivity.
Qed.
Lemma shiftₛ_projE {E} n f x :
  shiftₛ (VarE (E := E)) ZE_subst n (projE ∘ f) x =
  projE (shiftₛ (Var _) Z_subst n f x).
Proof.
  symmetry.
  apply (shiftₙₛ_natural (g:= projE)).
  - reflexivity.
  - intros g z.
    symmetry.
    apply ZE_subst_proj_proj.
Qed.

(* Lemma projE_subst_max_fv {E} *)
(*       (f g : nat -> ZE E)(z : Z _) *)
(*          (hfg : forall n, n <= max_fv z -> f n = g n) : *)
(*   projE z [f ]ₘ = projE z [f ]ₘ *)
Lemma ZE_ren_subst_eq {E} (f : nat -> nat) (x : ZE E) :
  ZE_ren f x = x [ fun n => VarE (f n) ]ₘ.
Proof.
  revert x.
  apply class_ind.
  intro z.
  fold (projE z).
  symmetry.
  etransitivity;[|apply  ZE_ren_proj].
  etransitivity;[apply ZE_subst_proj_proj|].
  f_equal.
  symmetry.
  apply Z_ren_subst_eq.
Qed.

Lemma ZE_ops_ren
  {E : equational_theory} (o : O (main_signature E)) (v : Vec (ZE E) (ar o)) (f : nat -> nat) :
    ZE_ren f (ZE_ops v) = ZE_ops (Vec_map (fun (n : nat) (t : ZE E) => ZE_ren (shiftₙ n f) t) v).
Proof.
  revert v.
  refine (vec_quot_ind _).
  intro v.
  rewrite ZE_ops_projE.
  rewrite <- ZE_ren_proj.
  cbn.
  rewrite <- ZE_ops_projE.
  f_equal.
  rewrite vec_map_map.
  rewrite vec_map_map.

  apply vec_map_fun_ext.
  intros.
  apply ZE_ren_proj.
Qed.

Lemma ZE_ops_subst
  {E : equational_theory} (o : O (main_signature E)) (v : Vec (ZE E) (ar o)) (f : nat -> ZE E) :
    ZE_ops v [f ]ₘ = ZE_ops (Vec_map (fun (n : nat) (t : ZE E) => t [shiftₛ VarE ZE_subst n f ]ₘ) v).
Proof.
  revert v.
  refine (vec_quot_ind _).
  intro v.
  rewrite ZE_ops_projE.
  rewrite ZE_subst_proj.
  cbn.
  f_equal.
  rewrite vec_map_map.
  apply vec_map_fun_ext.
  intros.
  symmetry.
  etransitivity.
  apply ZE_subst_proj.
  apply ZE_mixed_subst_ext.
  intro n.
  apply shiftₙₛ_ext.
  -  intros. symmetry. 
     apply ZE_ren_subst_eq.
  - reflexivity.
Qed.

Definition ZEModel_data (E : equational_theory) : model_data (main_signature E) :=
  {|
  carrier := ZE E;
  variables := VarE  ;
  ops := @ZE_ops E ;
  substitution := ZE_subst
  |}.


Fixpoint ZE_ren_mixed_subst {E} (g : nat -> nat) (f : nat -> ZE E) (z : Z _) :
  Z_ren g z ⟦ f ⟧ = z ⟦ fun n : nat => f (g n) ⟧.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_fun_ext.
    intros.
    cbn.
    etransitivity;[apply ZE_ren_mixed_subst|].
    apply ZE_mixed_subst_ext.
    intro n.
    (* ca devrait marcher *)
  unfold shiftₙ, shiftₙₛ.
  cbn -[leb].
  cbn -[leb].
  destruct (n <? a) eqn:eqna.
  + rewrite eqna; reflexivity.
  + cbn -[leb].
    case(Nat.ltb_spec _ _).
    * intro. exfalso. lia.
    * intros. f_equal.
      rewrite Nat.add_sub.
      reflexivity.
Qed.

Lemma ZE_ren_subst {E} (g : nat -> nat) (f : nat -> ZE E) (z : ZE E) :
ZE_ren g z [f ]ₘ = z [fun n : nat => f (g n) ]ₘ.
Proof.
  revert z.
  apply class_ind.
  intro z.
  fold (projE z).
  rewrite <- ZE_ren_proj.
  rewrite ZE_subst_proj.
  rewrite ZE_subst_proj.
  apply ZE_ren_mixed_subst.
Qed.
Lemma ZE_ren_ren {E} g f (z : ZE E) :
ZE_ren g (ZE_ren f z) = ZE_ren (g ∘ f) z.
  rewrite ZE_ren_subst_eq at 1.
  rewrite ZE_ren_subst.
  symmetry.
  apply ZE_ren_subst_eq.
Qed.
Fixpoint ZE_mixed_subst_ren 
  {E} (g : nat -> nat) (f : nat -> ZE E) z :
  ZE_ren g (z ⟦ f ⟧) = z ⟦ fun n : nat => ZE_ren g (f n) ⟧.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    rewrite ZE_ops_ren.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_fun_ext.
    intros.
    etransitivity.
    { apply ZE_mixed_subst_ren. }
    apply ZE_mixed_subst_ext.
    intro n.
    (* ca devrait marcher *)
  unfold shiftₙ, shiftₙₛ.
  cbn -[leb].
  cbn -[leb].
  destruct (n <? a) eqn:eqna.
  + rewrite ZE_ren_var;rewrite eqna; reflexivity.
  + cbn -[leb].
    rewrite 2 ZE_ren_ren.
    rewrite 2 ZE_ren_subst_eq.
    apply ZE_subst_ext.
    intro.
    unfold compose.
    cbn -[leb].
    f_equal.
    case(Nat.ltb_spec _ _).
    * intro. exfalso. lia.
    * intros. f_equal.
      rewrite Nat.add_sub.
      reflexivity.
Qed.
Lemma ZE_subst_ren
  {E} (g : nat -> nat) (f : nat -> ZE E) (z : ZE E) :
  ZE_ren g (z [f ]ₘ) = z [fun n : nat => ZE_ren g (f n) ]ₘ.
Proof.
  revert z.
  apply class_ind.
  intro z.
  fold (projE z).
  rewrite ZE_subst_proj.
  rewrite ZE_subst_proj.
  apply ZE_mixed_subst_ren.
  Qed.

Fixpoint ZE_mixed_subst_subst {E : equational_theory}
      (f g : nat -> ZE E) (z : Z _) :
  (z ⟦ g ⟧) [f ]ₘ = z ⟦ fun n : nat => g n [f ]ₘ ⟧.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    rewrite ZE_ops_subst.
    f_equal.
    rewrite vec_map_map.
    apply vec_map_fun_ext.
    intros a z.
    etransitivity.
    {apply ZE_mixed_subst_subst.}
    apply ZE_mixed_subst_ext.
    intro n.
  unfold shiftₛ, shiftₙₛ.
  case  (Nat.ltb_spec _ _) .
    + rewrite ZE_subst_var.
      case  (Nat.ltb_spec _ _).
      reflexivity.
      lia.
  + cbn -[leb].
    intros.
    rewrite ZE_ren_subst.
    rewrite ZE_subst_ren.
    apply ZE_subst_ext.
    intro.

    case(Nat.ltb_spec _ _).
    * intro. exfalso. lia.
    * intros. f_equal.
      rewrite Nat.add_sub.
      symmetry.
      apply ZE_ren_subst_eq.
Qed.
    (* ah mais c'est comme avant.. *)
Lemma ZE_subst_subst {E : equational_theory}
      (f g : nat -> ZE E) (x : ZE E) :
  (x [g]ₘ) [f]ₘ = x [fun n : nat => g n [f]ₘ]ₘ.
Proof.
  revert x.
  apply class_ind.
  intro z.
  fold (projE (E := E) z).
  rewrite ZE_subst_proj.
  rewrite ZE_subst_proj.
  apply ZE_mixed_subst_subst.
Qed.
Fixpoint ZE_mixed_subst_id {E}(z : Z _): z ⟦ VarE ⟧ = z / ZEr E.
Proof.
  destruct z.
  - reflexivity.
  - cbn.
    etransitivity;revgoals.
    apply ZE_ops_projE.
    f_equal.
    apply vec_map_fun_ext.
    intros n z.
    etransitivity;[|apply ZE_mixed_subst_id].
    apply ZE_mixed_subst_ext.
    intro m.
    apply shiftₙₛ_var.
    apply ZE_ren_var.
Qed.

Lemma ZE_subst_id {E} (z : ZE E) : z [VarE ]ₘ = z.
Proof.
  revert z.
  apply class_ind.
  intro z.
  etransitivity.
  apply ZE_subst_proj.
  apply ZE_mixed_subst_id.
Qed.
Program Definition ZEModel ( E : equational_theory) : model (main_signature E) :=
  {| data := ZEModel_data E ;
     laws := {|
              substitution_ext := @ZE_subst_ext E ;
              variables_subst := @ZE_subst_var E ;
              ops_subst := @ZE_ops_subst E ;
              assoc := @ZE_subst_subst E ;
              id_neutral := @ZE_subst_id E
            |}
  |}.

Definition projE_mor {E} : model_mor (ZModel _) (ZEModel E) :=
  {| carrier_mor := (projE : ZModel _ -> ZEModel E) ;
     substitution_mor := fun f z => eq_sym (ZE_subst_proj_proj f z) ;
     variables_mor := fun _ => eq_refl _  ;
     ops_mor := fun o v => eq_sym (ZE_ops_projE v)
  |}.


Fixpoint ini_mor_compat {E} (m : model_equational E)( x y : Z (main_signature E))(r :  ZEr E x y) :
  ini_mor m x = ini_mor m y.
Proof.
  induction r; try congruence.
  - cbn.
    etransitivity; revgoals.
    apply (lift_ops_natural _ (initial_morphism m)).
    etransitivity; revgoals.
    apply model_eq.
    symmetry.
    apply (lift_ops_natural _ (initial_morphism m)).
  - cbn.
    f_equal.
    induction H.
    + reflexivity.
    + cbn.
      f_equal.
      * apply ini_mor_compat; assumption.
      * assumption.
Qed.
Definition ini_morE {E} (m : model_equational E)(z : ZE E) : m.
  revert z.
  unshelve eapply factor.
  - apply (ini_mor).
  - apply ini_mor_compat.
Defined.

Lemma ini_morE_proj {E} (m : model_equational E) x :
  ini_morE m (x / ZEr E) = ini_mor m x.
Proof.
  apply factorize.
Qed.

(* TODO prouver  que les proj est un morphisme de modele*)
Lemma ini_morE_unique {E} (m : model_equational E)(f : model_mor (ZEModel E) m)(z : ZE E) :
f z = ini_morE m z.
  revert z.
  apply class_ind.
  intro x.
  cbn.
  rewrite ini_morE_proj.
  Abort.
(*
  apply factor_extens.
  revert z.
  unshelve eapply factor.
  - apply (ini_mor).
  - apply ini_mor_compat.
Defined.



*)












