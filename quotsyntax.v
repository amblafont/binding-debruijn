(**
Contents (with the example of lambda-calculus modulo β and η)
- Equational theory and models
- Syntax for an equational theory (as a quotient)
- Initiality of this syntax
*)

Require Import Arith.
Require Import Basics.
Require Import micromega.Lia.
 (* for composition *)
Open Scope program_scope.
Open Scope list_scope.

Require Import Lib.
Require Import Quot.
Require Import syntaxdb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* substitution in the quotiented syntax *)
Reserved Notation "x [ s ]ₘ" (at level 30).
(* mixed substitution in the syntax *)
Reserved Notation "x ⟦ s ⟧" (at level 30).


Record half_equation (S1 : signature)(S2 : signature) :=
  {
    lift_ops :> forall (m : model S1), forall (o : O S2), vec m (ar o) -> m;
    lift_ops_subst :
      forall (m : model S1) (o : O S2),
        binding_condition (variables m) (substitution (m := m))
                          (@lift_ops m o) ;
    lift_ops_natural : forall (m1 m2 : model S1) (f : model_mor m1 m2)
                         (o : O S2)(v : vec m1 (ar o)),
        lift_ops (vec_map (fun _ => f) v)  = f (lift_ops v)
                
  }.

Arguments lift_ops [S1 S2] h [m] o.

Record equational_theory :=
  { metavariables : signature ;
    main_signature : signature ;
    left_handside : half_equation main_signature metavariables ;
    right_handside : half_equation main_signature metavariables 
  }.

Inductive LCβη_metavariables_O := Beta | Eta.
Definition LCβη_metavariables : signature :=
  {|
    O := LCβη_metavariables_O ;
    ar := fun o => match o with
                  Beta =>
                  (* two metavariables in (λx) y = x[y],
                     with x binding a variable *)
                    1 :: 0 :: nil 
                | Eta => 0 :: nil
                  (* one metavariable: t = (λ(t[n ↦ n+1] 0) *)
                end
  |}.



Definition LCβη_left_handside_data (m : model LC_sig)(o : LCβη_metavariables_O)
  : vec m (ar (s := LCβη_metavariables) o) -> m :=
  match o with
    Beta => fun v =>
             let x := vec_hd v in
             let y := vec_hd (vec_tl v) in
             app (abs x) y
  | Eta => fun v => vec_hd v
  end.

Definition LCβη_right_handside_data (m : model LC_sig)(o : LCβη_metavariables_O)
  : vec m (ar (s := LCβη_metavariables) o) -> m :=
  match o with
    Beta => fun v =>
             let x := vec_hd v in
             let y := vec_hd (vec_tl v) in
             x [ fun n => match n with 0 => y | S p => variables m p end ]
  | Eta => fun v =>
            let t := vec_hd v in
            (abs (app (t [ fun n => variables m (1 + n) ]) (variables m 0)))
  end.


Program Example LCβη_sig : equational_theory :=
  {|
  main_signature := LC_sig;
  metavariables := LCβη_metavariables ;
  left_handside :=
    {|
      lift_ops := LCβη_left_handside_data
    |} ;
  right_handside :=
    {|
      lift_ops := LCβη_right_handside_data
    |} ;

  |}.
(**
Next come the proofs that the left handside and the right handside
are indeed half-equations.
 *)

Next Obligation .
  red.
  destruct o; cbn;intros f v.
  -  rewrite vec_tl_map, !vec_hd_map.
     unfold app, abs.
     do 2 (rewrite (ops_subst (mod_laws m)); cbn).
     reflexivity.
  - rewrite vec_hd_map.
    reflexivity.
Qed.
Next Obligation.
  destruct o; cbn.
  - rewrite vec_tl_map, !vec_hd_map.
    unfold app, abs.
    do 2 (rewrite (ops_mor (mor_laws f)); cbn).
    reflexivity.
  - rewrite vec_hd_map.
    reflexivity.
Qed.
Next Obligation .
  red.
  destruct o; cbn;intros f v.
  -  rewrite vec_tl_map, !vec_hd_map.
     do 2 rewrite (assoc (mod_laws m)); cbn.
     apply (substitution_ext (mod_laws m)).
     intro n.
     destruct n; cbn.
     + rewrite (variables_subst (mod_laws m)).
       reflexivity.
     + rewrite (variables_subst (mod_laws m)).
       rewrite (assoc (mod_laws m)); cbn.
       etransitivity.
       symmetry; apply (id_neutral (mod_laws m)).
       apply (substitution_ext (mod_laws m)).
       intro p.
       rewrite (variables_subst (mod_laws m)).
       reflexivity.
  - rewrite !vec_hd_map.
    unfold app, abs.
     do 2 (rewrite (ops_subst (mod_laws m)); cbn).
     rewrite (variables_subst (mod_laws m)).
     cbn.
     f_equal.
     f_equal.
     f_equal.
     f_equal.
     do 2 rewrite (assoc (mod_laws m)); cbn.
     apply (substitution_ext (mod_laws m)).
     intro n.
     destruct n; cbn.
     + rewrite (variables_subst (mod_laws m)).
       reflexivity.
     + rewrite (variables_subst (mod_laws m)).
       reflexivity.
Qed.
Next Obligation.

  destruct o; cbn.
  - rewrite vec_tl_map, !vec_hd_map.
    rewrite (substitution_mor (mor_laws f)); cbn.
    apply (substitution_ext (mod_laws _)).
    unfold compose.
    intro n.
     destruct n; cbn.
     + reflexivity.
     + rewrite (variables_mor (mor_laws _)).
       reflexivity.
  - rewrite !vec_hd_map.
    unfold app, abs.
    do 2 (rewrite (ops_mor (mor_laws f)); cbn).
    rewrite (variables_mor (mor_laws _)).
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    rewrite (substitution_mor (mor_laws f)); cbn.
    apply (substitution_ext (mod_laws _)).
    unfold compose.
    auto using (variables_mor (mor_laws _)).
Qed.


Record model_equational (E : equational_theory) :=
  { main_model :> model (main_signature E) ;
    model_eq : forall o (v : vec main_model (ar o)),
        left_handside E main_model o v = right_handside E main_model o v
  }.

Section LC_βη.
End LC_βη.

(** Equivalence relation on the main signature of an equational theory *)
Inductive rel_Z (E : equational_theory) : Z (main_signature E) -> Z (main_signature E) -> Prop :=
| eqE : forall o v, rel_Z (left_handside E (ZModel _) o v) (right_handside E (ZModel _) o v) 
| reflE : forall z, rel_Z z z
| symE : forall a b, rel_Z b a -> rel_Z a b
| transE : forall a b c, rel_Z a b -> rel_Z b c -> rel_Z a c
| congrE : forall (o : O (main_signature E)) (v v' : vec _ (ar o)),
    rel_vec (@rel_Z E)  v v' -> rel_Z (Op o v) (Op o v').



Definition ZEr (E : equational_theory) : Eqv (Z (main_signature E)) :=
  Build_Eqv (@rel_Z E) (@reflE E) (@symE E)(@transE E) .


(** Syntax for a quotiented signature *)
Definition ZE(E : equational_theory) := Z (main_signature E) // (ZEr E).

Example LCβη := ZE LCβη_sig.

Definition  projE{E : equational_theory} (z : Z (main_signature E)) : ZE E :=
  z / ZEr E.

Definition ZE_ops (E : equational_theory) (o : O (main_signature E)) (v : vec (ZE E) (ar o)) :
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
       (o : O (main_signature E)) (v : vec (Z (main_signature E)) (ar o)) :
  ZE_ops (vec_map (fun _ => projE) v) = projE (Op o v).

Proof.
  apply vec_quot_out_proj.
Qed.

Lemma lift_ops_Z_ren {S V : signature} (h : half_equation S V)
   (f : nat -> nat) (o : O V) v :
  Z_ren f (h (ZModel S) o v) = h (ZModel S) o (vec_map (fun n t => Z_ren (derivₙ n f) t) v).
Proof.
  etransitivity ; [apply Z_ren_subst_eq|].
  etransitivity ; [apply (lift_ops_subst _ (m := ZModel _) )|].
  f_equal.
  apply vec_map_ext.
  intros.
  symmetry.
  etransitivity ; [apply Z_ren_subst_eq|].
  apply Z_subst_ext.
  intro n.
  cbn.
  apply var_derivₙ.
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
                 (vec_map 
                    (fun n x =>
                       x ⟦ derivₙₛ VarE ZE_ren n f ⟧
                    ) v)
  end where "t ⟦ s ⟧" := (ZE_mixed_subst s t).

Fixpoint max_fv {S : signature} (z : Z S) : nat :=
  match z with
    Var _ n => n
  | Op op  v => vec_max (vec_map (fun n x => n + max_fv x) v)
  end.

Fixpoint ZE_mixed_subst_ext {E} (f g : nat -> ZE E)(z : Z _)
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
      * apply ZE_mixed_subst_ext.
        intros.
        apply derivₙₛ_ext.
        reflexivity.
        intros.
        apply hfg.
        lia.
      * apply IHv.
        cbn.
        intros.
        apply hfg.
        lia.
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
    apply vec_map_ext.
    intros n z.
    etransitivity;[ apply Z_subst_quot| ].
    cbn.
    apply ZE_mixed_subst_ext.
    intros m hm.
    unfold compose.
    apply derivₙₛ_natural.
    + reflexivity.
    + cbn.
      apply ZE_ren_proj.
Qed.



Fixpoint ZE_mixed_subst_compat
  (E : equational_theory) 
      (f : nat -> ZE E)(z z' : Z (main_signature E))(rz :ZEr E z z'): z ⟦ f ⟧ = z' ⟦ f ⟧.
Proof.
  destruct rz.
  - cbn.
    revert f.
    refine (finitary_seq_quot_ind _ (n := 1 + Nat.max (max_fv(left_handside E (ZModel (main_signature E)) o v))
                                  (max_fv (right_handside E (ZModel (main_signature E)) o v))) _ _).
    + intros f g hfg.
      erewrite 2 (ZE_mixed_subst_ext (f := f)(g := g)).
      * tauto.
      * intros; apply hfg; lia.
      * intros; apply hfg; lia.
    + intro h.
      do 2 rewrite <- (Z_subst_quot h).
      etransitivity.
      {
        apply (f_equal projE).
        apply  (lift_ops_subst _ (m := ZModel _) h v).
      }
      etransitivity;revgoals.
      {
        symmetry.
        apply (f_equal projE).
        apply  (lift_ops_subst _ (m := ZModel _) h v).
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
  auto.
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
Lemma derivₛ_projE {E} n f x :
  derivₛ (VarE (E := E)) ZE_subst n (projE ∘ f) x =
  projE (derivₛ (Var _) Z_subst n f x).
Proof.
  symmetry.
  apply (derivₙₛ_natural (g:= projE)).
  - reflexivity.
  - intros g z.
    symmetry.
    apply ZE_subst_proj_proj.
Qed.

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
  {E : equational_theory} (o : O (main_signature E)) (v : vec (ZE E) (ar o)) (f : nat -> nat) :
    ZE_ren f (ZE_ops v) = ZE_ops (vec_map (fun (n : nat) (t : ZE E) => ZE_ren (derivₙ n f) t) v).
Proof.
  revert v.
  refine (vec_quot_ind _ _).
  intro v.
  rewrite ZE_ops_projE.
  rewrite <- ZE_ren_proj.
  cbn.
  rewrite <- ZE_ops_projE.
  f_equal.
  rewrite vec_map_map.
  rewrite vec_map_map.

  apply vec_map_ext.
  intros.
  apply ZE_ren_proj.
Qed.

Lemma ZE_ops_subst
  {E : equational_theory} (o : O (main_signature E)) (f : nat -> ZE E)(v : vec (ZE E) (ar o))  :
    ZE_ops v [f ]ₘ = ZE_ops (vec_map (fun (n : nat) (t : ZE E) => t [derivₛ VarE ZE_subst n f ]ₘ) v).
Proof.
  revert v.
  refine (vec_quot_ind _ _).
  intro v.
  rewrite ZE_ops_projE.
  rewrite ZE_subst_proj.
  cbn.
  f_equal.
  rewrite vec_map_map.
  apply vec_map_ext.
  intros.
  symmetry.
  etransitivity.
  apply ZE_subst_proj.
  apply ZE_mixed_subst_ext.
  intros n hn.
  apply derivₙₛ_ext.
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
    apply vec_map_ext.
    intros.
    cbn.
    etransitivity;[apply ZE_ren_mixed_subst|].
    apply ZE_mixed_subst_ext.
    intros n hn.
    apply derivₙₛ_derivₙ.
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
    apply vec_map_ext.
    intros.
    etransitivity.
    { apply ZE_mixed_subst_ren. }
    apply ZE_mixed_subst_ext.
    intros n hn.
    apply ren_derivₙ_derivₙₛ.
    + intros; apply ZE_ren_var.
    + intros; apply ZE_ren_ren.
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
    apply vec_map_ext.
    intros a z.
    etransitivity.
    { apply ZE_mixed_subst_subst. }
    apply ZE_mixed_subst_ext.
    intros n hn.
    etransitivity.
    {
    apply ZE_subst_ext.
    intro.
    apply (derivₛ_eq (ren := ZE_ren)).
    apply ZE_ren_subst_eq.
    }
    cbn.
    eapply subst_derivₙₛ.
    + intros; apply ZE_subst_var.
    + intros; apply ZE_ren_subst.
    + intros; apply ZE_subst_ren.
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
    apply vec_map_ext.
    intros n z.
    etransitivity;[|apply ZE_mixed_subst_id].
    apply ZE_mixed_subst_ext.
    intros m hm.
    apply derivₙₛ_var.
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
  {| mod_carrier := ZEModel_data E ;
     mod_laws := {|
              substitution_ext := @ZE_subst_ext E ;
              variables_subst := @ZE_subst_var E ;
              ops_subst := @ZE_ops_subst E ;
              assoc := @ZE_subst_subst E ;
              id_neutral := @ZE_subst_id E
            |}
  |}.


Program Definition projE_is_model_mor {E} :
  @is_model_mor _ (ZModel (main_signature E)) (ZEModel E) projE :=
  {|
  substitution_mor := fun f z => eq_sym (ZE_subst_proj_proj f z) ;
  variables_mor := fun _ => eq_refl _  ;
  ops_mor := fun o v => eq_sym (ZE_ops_projE v) |}.

Definition projE_mor {E} : model_mor (ZModel _) (ZEModel E) :=
  {| mor_carrier := (projE : ZModel _ -> ZEModel E) ;
     mor_laws := projE_is_model_mor 
  |}.

Lemma ZE_model_eq 
  (E : equational_theory)
  (o : O (metavariables E))
  (v : vec (ZE E) (ar o))
  : 
  left_handside E (ZEModel E) o v = right_handside E (ZEModel E) o v.
Proof.
  revert v.
  refine (vec_quot_ind _ _).
  intro v.
  rewrite 2 (lift_ops_natural _ (projE_mor (E := E))).
  apply class_eq.
  constructor.
Qed.
Definition  ZEModel_equational ( E : equational_theory) : model_equational E :=
  {| main_model := ZEModel E ;
     model_eq :=  @ZE_model_eq E
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

Fixpoint ini_mor_subst_ext {S : signature}(m : model S)(z : Z S)(f g : nat -> m)
  (fgeq: forall n, n <= max_fv z -> f n = g n) {struct z} : ini_mor m z [ f ] = 
                                         ini_mor m z [ g ].
Proof.
  destruct z.
  - cbn.
    rewrite 2 variables_subst ; try apply mod_laws.
    apply fgeq.
    cbn.
    reflexivity.
  - cbn.
    rewrite 2 ops_subst; try apply mod_laws.
    revert fgeq.
    cbn.
    intros.
    f_equal.
    rewrite 2 vec_map_map.
    induction v.
    + reflexivity.
    + cbn.
      f_equal.
      * apply ini_mor_subst_ext.
        intros.
        apply derivₙₛ_ext.
        -- reflexivity.
        -- intros.
           apply fgeq.
           cbn.
           lia.
      * apply IHv.
        cbn.
        intros.
        apply fgeq.
        cbn.
        lia.
Qed.
    

Lemma ini_morE_is_model_mor {E} (m : model_equational E)
      : @is_model_mor _ (ZEModel E) m (ini_morE m).
Proof.
  split; cbn.
  - intro n.
    etransitivity.
    apply ini_morE_proj.
    reflexivity.
  - intros.
    revert x.
    apply class_ind.
    intro x.
    revert f.
    rewrite ini_morE_proj.
    fold (projE x).
    refine (finitary_seq_quot_ind _ (n := 1 + max_fv x) _ _ ).
    + intros f g hfg.
      rewrite 2 ZE_subst_proj.
      rewrite (ZE_mixed_subst_ext (f := f)(g := g)); [| intros; apply hfg; lia].
      rewrite (ini_mor_subst_ext (S := main_signature E)(m := m) (z := x)
                                    (f := ini_morE m ∘ f)
                                    (g := ini_morE m ∘ g)).
      * tauto.
      * intros.
        unfold compose.
        rewrite hfg.
        reflexivity.
        lia.
    + intros.
      change (fun n => f n / ZEr E) with (compose (projE (E := E)) f).
      rewrite ZE_subst_proj_proj.
      etransitivity; revgoals.
      {
        apply substitution_ext;[apply mod_laws|].
        intro.
        symmetry.
        apply ini_morE_proj.
      }
      etransitivity; [apply ini_morE_proj|].
      apply ini_mor_subst.
  - intros.
    cbn.
    revert v.
    eapply (vec_quot_ind).
    intro v.
    rewrite ZE_ops_projE.
    etransitivity.
    apply ini_morE_proj.
    cbn.
    rewrite vec_map_map.
    f_equal.
    apply vec_map_ext.
    intros.
    symmetry.
    apply ini_morE_proj.
Qed.

Program Definition ini_morE_model_mor {E} (m : model_equational E)
  : model_mor (ZEModel E) m :=
  {| mor_carrier := ini_morE m ;
     mor_laws := ini_morE_is_model_mor m;
  |}.

Lemma ini_morE_unique {E} (m : model_equational E)(f : model_mor (ZEModel E) m)(z : ZE E) :
f z = ini_morE m z.
  revert z.
  apply class_ind.
  intro x.
  cbn.
  rewrite ini_morE_proj.
  apply (initial_morphism_unique (f := f ∘ projE_mor)).
  apply is_model_mor_compose; apply mor_laws.
Qed.














