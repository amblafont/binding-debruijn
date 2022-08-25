(**
Let L be the free Σ-monoid on Set^ℕ, with T the monad


We are given a parallel pair Ly₀ ⇉ LV
where V : ℕ → Set returns the set of metavariables with given arity.
What we want is not just a weak coequaliser in Kl(T), in the sense that
the output morphism is not unique, (induces a weak coequaliser in T-alg)
but true coequaliser in Kl(T).
Indeed, it seems we can prove that if t[ σ]ₘ = t[δ]ₘ, then σ and δ
coincide on each metavariable that appears in t. From that we can deduce uniqueness.


TODO: voir samemvar.json pour une tentative de preuve categorique
que le cas same metavariable est correct

*)

Require Import Arith.
Require Import Basics.
Require Import micromega.Lia.
Require Import Decidable.
From Equations Require Import Equations.

Open Scope program_scope.
Open Scope list_scope.

Require Import Lib.
Require Import syntaxdb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Maybe we could instead consider the following syntax:
Inductive Z : Type :=
  Var : nat -> Z
| Op : nat -> list (nat, Z) -> Z
| MVar : nat -> list Z -> Z
So we could do it in Isabelle!
 *)


  Theorem proj1 {A B}: A /\ B -> A.
  Proof.
    destruct 1; trivial.
    Defined.
  Theorem proj2 {A B}: A /\ B -> B.
  Proof.
    destruct 1; trivial.
    Defined.

Reserved Notation "x [ s ]ₘ" (at level 30).

(* Coercion Bool.Is_true : bool >-> Sortclass. *)
Coercion is_true : bool >-> Sortclass.

Lemma not_bool_eq (P : bool) : ~ P -> P = false.
  Abort.
(* TODO *)
Lemma irrelevance_bool (b : bool)(A B : b) : A = B.
  apply eqdec_uip.
  eauto with typeclass_instances.
Qed.

(* Class EqDec A := deceq : forall o o' : A,{ o = o'} + { o <> o' }. *)
(* Instance deceq_nat : EqDec nat := Nat.eq_dec. *)


Coercion sum_to_bool A B (b : { A } + { B }) : bool := if b then true else false.

(*
Lemma dec_to_bool_inj {P } (b b' : {P} + {~ P}) : (b : bool) = b' -> b = b'.
  Proof.
    intro eqb.
    revert b' eqb.
    refine (match b as b0 return match b0 with  with left p => _ | right p => _ end).
    destruct b,b'; try congruence.
    Set Printing Coercions.
    cbn in eqb.
    Abort.
*)

Infix "=m" := eq_dec (at level 70).
Notation "x '<>m' y" := (negb (sum_to_bool (x =m y))) (at level 70).

Lemma neq_negb_deceq {O}{_ : EqDec O} o' o (eqo : o' <> o) : o' <>m o.
  destruct (o' =m o); easy.
Qed.

(* TODO *)
Lemma neq_negb_deceq_false {O}{_ : EqDec O} o' o (eqo : o' <> o) : (o' =m o) = right eqo.
  Admitted.



Instance subdeceq {A}{_ : EqDec A} (P : A -> bool) : EqDec { a : A | P a}.

intros [a Pa] [a' Pa'].
destruct (a =m a') as [h|h].
- left.
  revert Pa.
  rewrite h.
  intros.
  f_equal.
  apply irrelevance_bool.
- right.
  intro.
  apply h.
  congruence.
Defined.


Instance deceq_option {A}{_ : EqDec A} : EqDec (option A).
intros a a'.
decide equality.
Defined.

Lemma deceq_eq_true {A}{_ : EqDec A} (a b: A) (eqb : a = b): a =m b = left eqb. 
  Admitted.

Lemma refl_deceq_true {A}{_ : EqDec A} (a : A) : a =m a = left eq_refl. 
  apply deceq_eq_true.
  Qed.
(*
Definition refl_deceq {A}{_ : EqDec A} (a : A) : a =m a. 
  cbn.
  destruct (a=m a).
  cbn.
  tauto.
  cbn.
  tauto.
  Defined.

Lemma uip_deceq {A}{_ : EqDec A} (a : A)(p : a =m a) : p = refl_deceq a.
Admitted.
*)

Fixpoint next_fv {S : signature} (z : Z S) : nat :=
  match z with
    Var _ n => 1 + n
  | Op op v => vec_max (vec_map (fun n x => next_fv x - n) v)
  end.

Inductive In_fv {S } (p : nat) : Z S -> Prop :=
  fv_var : In_fv p (Var _ p)
| fv_op : forall (o : O S) (v : vec (Z S) (ar o)), In_fv_vec p v ->
                                                  In_fv p (Op o v)
with In_fv_vec {S } (p : nat) : forall (l : list nat), vec (Z S) l -> Prop :=
| fv_hdV : forall a b l v, In_fv (p + a) b -> In_fv_vec p (ConsV a (lA := l) b v)
| fv_tlV : forall a b l v, In_fv_vec p v -> In_fv_vec p (ConsV a (lA := l) b v).

(*
Fixpoint in_fv {S}(p : nat) (t : Z S) : Prop :=
  match t with
    Var _ q => q = p
  | Op _ v => In_fv_vec p v
    end.
*)

(*
Lemma In_fv_Op {S} (p : nat) {o}(v : vec (Z S) (ar (s := S) o)) : In_fv p (Op o v) <-> In_fv_vec p v.
  Admitted.
*)



Lemma In_fv_neq_subst {S} p (t : Z S) :
  In_fv p t -> t [ fun n => if n =m p then Var _ (n + 1) else Var _ n ]ₛ <> t.
Admitted.
Lemma neq_subst_In_fv {S'} p (t : Z S') :
        (* (forall f, f p <> p -> t [ fun n => Var _ (f n) ]ₛ <> t) -> *)
        ( t [ fun n => Var _ (if n =m p then S n else n) ]ₛ <> t) ->
        In_fv p t.
  (*
with neq_subst_In_fv_vec {S'} p (l : list nat)(v : vec (Z S') l) :
  (* (forall f, f p <> p -> *)
  (
        (* vec_map (fun (n : nat) (b : Z S') => b [derivₙₛ (Var S') Z_ren n (fun n0 : nat => Var S' (f n0)) ]ₛ) v *)
        vec_map (fun (n : nat) (b : Z S') => b [derivₙₛ (Var S') Z_ren n (fun n0 : nat => Var S' (if n0 =m p then S n0 else n0)) ]ₛ) v
                 <> v
  ) ->
        In_fv_vec p v.
*)
  Admitted.
Corollary neq_subst_In_fv_vec {S'} p (l : list nat)(v : vec (Z S') l) :
  (* (forall f, f p <> p -> *)
  (
        (* vec_map (fun (n : nat) (b : Z S') => b [derivₙₛ (Var S') Z_ren n (fun n0 : nat => Var S' (f n0)) ]ₛ) v *)
        vec_map (fun (n : nat) (b : Z S') => b [derivₙₛ (Var S') Z_ren n (fun n0 : nat => Var S' (if n0 =m p then S n0 else n0)) ]ₛ) v
                 <> v
  ) ->
        In_fv_vec p v.
Proof.
  induction v.
  - cbn.
    contradiction.
  - cbn.
    Admitted.
(*
  {
    destruct t.
    - cbn.
      intro h.
      specialize (h (fun q => if p =m q then 1+q else q)).
      revert h.
      cbn.
      rewrite refl_deceq_true.
      cbn.
      destruct (p =m n).
      + subst.
        constructor.
      + intro h.
        exfalso.
        apply h.
        * apply Nat.neq_succ_diag_l.
        * reflexivity.
    - cbn.
      intro h.
      assert (h' :
                forall f : nat -> nat,
      f p <> p ->
       (vec_map (fun (n : nat) (b : Z S') => b [derivₙₛ (Var S') Z_ren n (fun n0 : nat => Var S' (f n0)) ]ₛ) v) <>
       v
).
      admit.
      constructor.
      revert h'.
      clear h.
      induction v.
      + cbn.
        intro h.
        exfalso.
        apply (h S).
        apply Nat.neq_succ_diag_l.
        reflexivity.
      + cbn.
        Admitted.


        speicalise
      eapply neq_subst_In_fv_vec.
      exact h'.
  }
  {
    Guarded.
    
  }
Admitted.
*)

Fixpoint Z_in_fv_subst_ext {S'} (f g : nat -> Z S')(z : Z S')
         (hfg : forall n, In_fv n z -> f n = g n) {struct z} :
  z [ f ]ₛ= z [ g ]ₛ.
  Proof.
  (*
with Z_in_fv_subst_ext_vec {S'} (f g : nat -> Z S')(l : list nat)(v : vec (Z S') l)
         (hfg : forall n, In_fv_vec n v -> f n = g n) {struct v} :
  True.
  vec_map (fun _ =)z [ f ]ₛ= z [ g ]ₛ.
Proof.
*)
  destruct z.
  - cbn in hfg.
    cbn.
    apply hfg.
    constructor.
  - cbn.
    f_equal.
    cbn in hfg.
    assert (hfg' : forall n, In_fv_vec n v -> f n = g n).
    {
      intros n h.
      apply hfg.
      constructor.
      assumption.
    }
    clear hfg.
    revert hfg'.
    revert v.
    cbn.
    generalize (ar o).
    refine (fix rec_vec l v {struct v} := _) .
    destruct v.
    + reflexivity.
    + cbn.
      intro hfg.
      assert (hz : forall n, In_fv (n + a) z -> f n = g n).
      {
        intros.
        apply hfg.
        apply fv_hdV.
        assumption.
      }
      f_equal.
      * apply Z_in_fv_subst_ext.
        intros.
        apply derivₙₛ_ext_exact.
        reflexivity.
        intros.
        apply hz.
        rewrite Nat.sub_add.
        assumption.
        assumption.
      * apply rec_vec.
        intros.
        apply hfg.
        apply fv_tlV.
        assumption.
Qed.
(* signature for metavariables *)
Record msignature :=
  { Om : Type;
    Om_dec :> EqDec Om;
    arm : Om -> nat}.


Existing Instance Om_dec.

Definition extend_msig (V : msignature) (n : nat) : msignature :=
  {| Om := option (Om V); arm := fun o => match o with None => n | Some o' => arm o' end |}.

Notation "V +{ n }" := (extend_msig V n) (at level 30).

Definition msignature_without (V : msignature) (o : Om V) : msignature :=
  {| Om := { v | v <>m o}; arm := fun o' => arm (proj1_sig o') |}.

Infix "\" := @msignature_without (at level 30).

Coercion signature_from_msignature (V : msignature) :=
  {| O := Om V; ar := fun m => List.repeat 0 (arm m) |}.

Inductive sumSigO (S : signature)(V : msignature) :=
   SOp : O S -> sumSigO S V 
 | SMVar : Om V -> sumSigO S V.

Arguments SOp [S] [V].
Arguments SMVar [S] [V].

Definition sumSig (S : signature)(V : msignature) :=
  {| O := sumSigO S V ; ar := fun o => match o with SOp o' => ar o' | SMVar o' => ar (s := signature_from_msignature V) o' end |}.

Delimit Scope signature_scope with s.
Infix "+" := sumSig : signature_scope.
Notation "'vecn' x n" := (vec x (List.repeat 0 n)) (x at next level, n at next level, at level 1).
Notation "x ** n" := (vecn x n) ( at level 40).

Definition T (S : signature)(V : msignature) := Z (S + V)%s.

Definition mops [S V][m : model_data (S + V)%s] (o : O S) (v : vec m (ar o)) : m :=
  ops (S := (S + V)%s) (SOp o) v.

Arguments mops [S V m] o.

Definition mvar [S V][m : model_data (S + V)%s] (o : Om V) (v : m ** arm o) : m :=
  ops (S := (S + V)%s) (SMVar o) v.

Arguments mvar [S V m] o.

Definition TOp {S V} (o : O S) (v : vec (T S V) (ar o)) : T S V :=
  mops (m := ZModel (S + V)%s) o v.

Definition TMVar {S V} (o : Om V) (v : T S V ** arm o) : T S V :=
  mvar (m := ZModel (S + V)%s) o v.

Fixpoint vec_nth {A B}(default : B)(l : list A)(v : vec B l)(n : nat) {struct v} : B :=
  match v with
    NilV => default
  | ConsV a b lB => match n with 0 => b | S p => vec_nth default lB p end
    end.

Fixpoint vec_mk {A B} n (f : nat -> A -> B)(l : list A) : vec B l :=
  match l with
    nil => NilV
  | cons a lA => ConsV a (f n a) (vec_mk (S n) f lA)
  end.

Definition vec_range0 {S}(m : model_data S)(n : nat) :=
vec_mk 0 (fun n0 _ : nat => variables m n0) (List.repeat 0 n).

Fixpoint vec_mk_ext_exact {A B} n (f g : nat -> A -> B)(l : list A) :
  (forall p a, p < n + length l -> p >= n -> f p a = g p a) -> vec_mk n f l = vec_mk n g l.
  refine
  (match l with
    nil => _
  | cons a lA => _
  end).
  reflexivity.
  cbn.
  intro hfg.
  f_equal.
  - apply hfg.
    + lia.
    + lia.
  - apply vec_mk_ext_exact.
  intros.
  apply hfg.
  lia.
  lia.
  Qed.

Lemma vec_mk_ext {A B} n (f g : nat -> A -> B)(l : list A) :
  (forall p a, p >= n -> f p a = g p a) -> vec_mk n f l = vec_mk n g l.
  intro H.
  eapply vec_mk_ext_exact.
  intros.
  apply H.
  assumption.
Qed.

Fixpoint vec_mk_eqf {A B} n (f : nat -> A -> B)(l : list A) :
  vec_mk n f l = vec_mk 0 (fun p => f (n + p)) l.
  Proof.
  destruct l.
  - reflexivity.
  - cbn.
    f_equal.
    f_equal.
    apply plus_n_O.
    rewrite (vec_mk_eqf _ _ (S n)).
    rewrite (vec_mk_eqf _ _ 1).
    cbn.
    apply vec_mk_ext.
    intros.
    f_equal.
    lia.
  Qed.

Fixpoint vec_nth_mk {A B}(default : B)(l : list A)(f : nat -> A -> B)(n m : nat) {struct l} :
  vec_nth default (vec_mk n f l) m = match List.nth_error l m with
                                       None => default
                                     | Some a => f (m + n) a end.
  (* if m <? List.length l ntthen f (m + n) else default. *)
  refine
  (match l with
    nil => _
  | cons a lA => _
  end).
  destruct m; intros; reflexivity.
  cbn.
  destruct m.
  reflexivity.
  cbn.
  etransitivity.

  apply vec_nth_mk.
  rewrite <- plus_Snm_nSm.
  reflexivity.
Qed.

Fixpoint vec_mk_nth {A B}(default : nat -> B)(l : list A)(v : vec B l) m {struct v} :
  vec_mk m (fun n a => vec_nth (default n) v (n - m)) l = v.
  refine (
    match v with
    NilV => _
  | ConsV a b lB => _
    end).
  reflexivity.
  cbn.
  rewrite <- minus_diag_reverse.
  cbn.
  f_equal.
  etransitivity.
  {
  eapply (vec_mk_ext (g := fun n _ => vec_nth (default n) lB (n - S m))).

  intros.
  destruct (p - m) eqn:e.
  - exfalso.
    lia.
  - f_equal.
    lia.
    }
  apply vec_mk_nth.
  Qed.



Lemma vec_mk_nth0 {A B}(default : nat -> B)(l : list A)(v : vec B l)  :
  vec_mk 0 (fun n a => vec_nth (default n) v n) l = v.
  etransitivity;revgoals.
  eapply vec_mk_nth.
  apply vec_mk_ext.
  intros.
  f_equal.
  apply minus_n_O.
Qed.

Fixpoint vec_mk_repeat {A B}a (f : nat -> A -> B)(n m : nat) :
   vec_mk n f (List.repeat a m) = vec_mk n (fun n _ => f n a)(List.repeat a m).
  destruct m.
  reflexivity.
  cbn.
  f_equal.
  apply vec_mk_repeat.
Qed.


Fixpoint vec_map_mk {A B C} (g : A -> B -> C) n (f : nat -> A -> B)(l : list A) :
  vec_map g (vec_mk n f l) = vec_mk n (fun n a => g a (f n a)) l.
  refine
  (match l with
    nil => _
  | cons a lA => _
  end).
  cbn.
  reflexivity.
  cbn.
  f_equal.
  apply vec_map_mk.
Qed.


Definition an_assignation {S} n (m : model_data S) :=
   m ** n  -> m.

Definition assignation {S} V (m : model_data S) :=
  forall o : Om V, an_assignation (arm o) m.

Definition an_assignation_laws {S n m} (a : @an_assignation S n m) :=
     binding_condition (variables m) (substitution (m := m)) a.

Definition assignation_laws {S V m} (a : @assignation S V m) :=
     forall o , an_assignation_laws (a o).

(* Definition an_assignation_raw {S}V n (m : model_data S) := *)
(*    Om V -> m. *)

Definition assignation_raw {S} V (m : model_data S) :=
   Om V  -> m.

Definition vec_to_ren {S}{m : model_data S}{l : list nat}(v : vec m l) : nat -> m :=
    fun n => vec_nth (variables _ n) v n. 

Definition mk_an_assignation {S n } {m : model_data S} (a : m) : an_assignation n m.
intro v.
refine (a [ vec_to_ren v]).
Defined.

Definition mk_assignation {S V } {m : model_data S} (a : assignation_raw V m) : assignation V m.
intro o.
apply mk_an_assignation.
exact (a o).
Defined.

Definition mk_an_assignation_raw {S n} {m : model_data S} (a : an_assignation n m) : m.
(* intro o. *)
  apply a.
  apply vec_range0.
Defined.

Definition mk_assignation_raw {S V } {m : model_data S} (a : assignation V m) : assignation_raw V m.
intro o.
eapply mk_an_assignation_raw.
exact (a o).
Defined.

Lemma vec_to_ren_vec_range0{S n}(m : model_data S) p :
  vec_to_ren (vec_range0 m n) p = variables m p.
Proof.
  unfold vec_to_ren.
  unfold vec_range0.
  rewrite vec_nth_mk.
  rewrite <- plus_n_O.
  destruct (List.nth_error _ _); reflexivity.
Qed.
Lemma an_assignation_raw_inverse {S n}{m : model S}(a : m) :
   mk_an_assignation_raw (mk_an_assignation (n := n) a) = a.
Proof.
  unfold mk_an_assignation.
  unfold mk_an_assignation_raw.
  etransitivity; [|apply (id_neutral (mod_laws m))].
  apply (substitution_ext(mod_laws m)).
  intro p.
  apply vec_to_ren_vec_range0.
  Qed.

Lemma assignation_raw_inverse {S V}{m : model S}(a : assignation_raw V m) :
  forall o, mk_assignation_raw (mk_assignation a) o = a o.
Proof.
  intro o.
  apply an_assignation_raw_inverse.
Qed.
Lemma an_assignation_raw_inverse' {S n}{m : model S}(a : an_assignation n m)(alaws : an_assignation_laws a) :
  forall  (v : m ** n), mk_an_assignation (mk_an_assignation_raw a) v = a v.
  Proof.
  intros  v.
  unfold mk_assignation.
  unfold mk_assignation_raw.
  etransitivity.
  apply alaws.
  f_equal.
  cbn.
  etransitivity.
  apply vec_map_mk.
  cbn.
  etransitivity.
  apply vec_mk_ext.
  intros.
  etransitivity.
  apply (variables_subst (mod_laws m)).
  cbn.
  reflexivity.
 etransitivity.
  apply vec_mk_repeat.
  cbn.
  apply vec_mk_nth0.
  Qed.

Lemma assignation_raw_inverse' {S V}{m : model S}(a : assignation V m)(alaws : assignation_laws a) :
  forall (o : Om V) (v : m ** arm o), mk_assignation (mk_assignation_raw a) v = a o v.
  intro.
  apply an_assignation_raw_inverse'.
  apply alaws.
  Qed.
(** !!! tres etonnant cet iso !!

 Ah oui, mais le mk_assignation verifie la loi seulement si le input
n'a pas trop de fv
 *)


Lemma assignation_fv {S n W} (a : an_assignation n (Z_model_data (S + W)%s))
      (alaws : an_assignation_laws a) : forall p v, In_fv p (a v) -> In_fv_vec p v.
intros p v in_pav.
eapply neq_subst_In_fv_vec.
apply In_fv_neq_subst in in_pav.
intro h.
apply in_pav.
etransitivity.
{ apply alaws. }
f_equal.
etransitivity; [|exact h].
cbn.
apply vec_map_ext.
intros a' b'.
cbn.
unfold derivₛ.
cbn.
apply Z_subst_ext.
intro q.
apply derivₙₛ_ext_exact.
- intros.
  symmetry.
  apply Z_ren_subst_eq.
- intro hq.
  cbn.
  destruct (_ =m _); f_equal.
  lia.
  Qed.


Definition id_assignation {S V} (m : model_data (S + V)%s) : assignation V m :=
  mvar (m := m).

Definition pull_model {S V} (m : model_data (S + V)%s) : model_data S :=
  {| carrier := m;
    variables := variables m;
    ops := fun o => ops (m := m) (SOp o);
    substitution := substitution (m := m) |}.

Notation "V ^* m" := (pull_model (V := V) m) (at level 40, left associativity).

Definition push_model {S V } {m : model_data S} (mop : assignation V m) : model_data (S + V)%s.
  refine 
  {| carrier := m;
    variables := variables m;
    ops := fun (o : O (S + V)%s) => match o with SOp o' => _ | SMVar o' => _ end;
    substitution := substitution (m := m) |}.
  exact (ops (m := m) o').
  apply mop.
  Defined.

Notation "a _! m" := (push_model (m := m) a) (at level 40, left associativity).

(*
Fixpoint msubst {S : signature}{V : msignature} {W : msignature} (f : assignation S V W)  (t : T S V)  { struct t} : T S W
  :=
  match t with
    Var n => Var n
  | Op op v => Op op
                 (vec_map 
                    (fun n b =>
                       ( b  [ f ]ₘ)
                    ) v)
  | MVar m v => f m v
  end
    where "t [ f ]ₘ" := (msubst f t).
*)


(*



*)


Definition msubst {S : signature}{V : msignature} {W : msignature}(m : model_data (S + W)%s) (f : assignation V m)(t : T S V)  : m.
  set (m' := (pull_model m)).
  apply (ini_mor (f _! m')).
  exact t.
  Defined.


(* Fixpoint msubst' {S : signature}{V : msignature} {W : msignature}(m : model_data (S + W)%s) (f : assignation V m)(t : T S V)  : m. *)
Fixpoint msubst' {S : signature}{V : msignature} {W : msignature}(m : model_data (S + W)%s) (f : assignation V m)(t : T S V)  : m.
  refine (
  match t with
    Var _ n => variables m n
  | Op o v =>
      match o with
        SOp o => fun v => _
      | SMVar o => fun v => _
      end v
  end).
  exact (ops (m := m) (SOp o) (vec_map (fun _ => msubst' _ _ _ m f) v)).
  eapply f.
  exact (vec_map (fun _ => msubst' _ _ _ m f) v).
Defined.
Notation "t [ f ]ₘ" := (msubst' f t).

Fixpoint msubst_eq {S : signature}{V : msignature} {W : msignature}(m : model_data (S + W)%s) (f : assignation V m)(t : T S V)  : msubst f t = msubst' f t .
induction t.
- reflexivity.
- destruct o; cbn.
  + f_equal.
  apply vec_map_ext.
  intros.
  apply msubst_eq.
  + f_equal.
  apply vec_map_ext.
  intros.
  apply msubst_eq.
  Qed.

Lemma msubst'_id {S : signature}{V : msignature}  (t : T S V)  : t [ id_assignation (m := Z_model_data _)]ₘ = t.
Admitted.

Lemma msubst'_ren {S : signature}{V W : msignature}(m : model_data (S + W)%s)(a : assignation V m) f
      (t : T S V) : t [ a ]ₘ [ fun x => variables m (f x) ] = 
                       t [ fun x => Var _ (f x) ]ₛ [ a ]ₘ .
Admitted.


Definition assignation_raw_comp {S V W1 W2}
           {m : model_data (S + W2)%s}
           (* {m : model_data S} *)
  (a1 : assignation_raw V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 m) : assignation_raw V m.
intro o.
set (t := a1 o).
refine (t [ a2 ]ₘ).
Defined.


(*
Si V = { n }
   W1 = {p}
   W2 = {q}, alors
a₁ ∘ a₂ (\vec{t}) = N(0,…,n-1)[ a₁ ]ₘ [ \vec{t} ]

 *)
(* push a1 along a2 *)
Definition assignation_comp {S V W1 W2}
           {m : model_data (S + W2)%s}
           (* {m : model_data S} *)
  (a1 : assignation V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 m) : assignation V m.
  apply mk_assignation.
  eapply assignation_raw_comp.
  exact (mk_assignation_raw a1).
  exact a2.
Defined.

Infix "∘a" := assignation_comp (at level 30).

Lemma assignation_comp_assoc {S V W1 W2 W3} {m : model_data (S + W3)%s}
  (a1 : assignation V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 (ZModel (S + W2)%s))
  (a3 :assignation W2 m)
  : a1 ∘a (a2 ∘a a3) = (a1 ∘a a2) ∘a a3.
Admitted.

Lemma assignation_comp_idr {S V W} 
  (a1 : assignation V (Z_model_data (S + W)%s)) 
   : a1 ∘a id_assignation (m := _) = a1.
  Admitted.
Lemma assignation_comp_idl {S V W} {m : model_data (S + W)%s}
  (a1 : assignation V m) 
   : id_assignation (m := _) ∘a a1  = a1.
  Admitted.

(*
  S : signature
  eqO : forall x y : O S, {x = y} + {x <> y}
  V : msignature
  o : Om V
  a : T S (V \ o)
  o' : Om V
  e : o' = o
  ============================
  an_assignation (arm o') (ZModel (S + V \ o)%s)
*)
Definition ass_instantiate1 {S}{V} {o o' : Om V}(a : T S (V \ o)) :
  an_assignation (arm o') (ZModel (S + V \ o)%s).
   apply mk_an_assignation.
   exact a.
Defined.

Definition ass_instantiate2 {S}{V} {o o' : Om V}(a : T S (V \ o)) 
  (eqo : o' <> o) :
  an_assignation (arm o') (ZModel (S + V \ o)%s).
   hnf.
   unshelve eset (o'' := exist _ o' _ : O (V \ o) ).
   { cbn.
     apply neq_negb_deceq.
     assumption.
   }
   change (arm o') with (arm o'').
   apply TMVar.
   Defined.
Definition assignation_instantiate 
           {S}
  {V : msignature}
  (o : Om V)
  (a : T S (V \ o))
  : assignation V (ZModel (S + V \ o)%s).
 intro o'.
 (* generalize (fun P => TMVar (S := S)(V := V \ o)(o := exist _ o' P)). *)
 cbn.
 destruct (o' =m o).
 - apply ass_instantiate1.
         (*
   intro.
   apply mk_an_assignation.
*)
   exact a.
   (* apply mk_an_assignation. *)
 - apply ass_instantiate2.
   cbn.
   (*
   intro h.
   refine( h _).
*)
   easy.
   easy.
   Defined.

Definition assignation_omit {S V W} (m : model_data (S + W)%s)
           (a : assignation  V m)
           (o : Om V) :
  assignation  (V \ o) m.
Proof.
  intros o' v.
  cbn in o'.
  apply (a (proj1_sig o')).
  exact v.
Defined.

Lemma assignation_omit_laws {S V W} (m : model_data (S + W)%s)
           (a : assignation  V m)
           (alaws : assignation_laws a)
           (o : Om V) :
  assignation_laws (assignation_omit a (o := o)).
Proof.
  intros o' s v.
  cbn.
  unfold assignation_omit.
  apply alaws.
Qed.

(* TODO: remove this lemma (it requires funext) *)
Lemma assignation_ext {S V W} (m : model_data (S + W)%s)
      (a b : assignation V m) :
  (forall o v, a o v = b o v) -> a = b.
Admitted.

Lemma assignation_omit_postcomp {S V W1 W2} (m : model_data (S + W2)%s)
           (a : assignation V (Z_model_data (S + W1)%s))
           (a' : assignation W1 m)
           (o : Om V) :
  assignation_omit (a ∘a a') (o := o) = assignation_omit a (o := o) ∘a a'.
apply assignation_ext.
intros o' v.
reflexivity.
Qed.

Definition assignation_incl {S V } (o : Om V) (m : model_data (S + V)%s) : assignation (V \ o) m.
  apply assignation_omit.
  apply id_assignation.
Defined.





(*
Lemma instantiate_omit_eq {S V W} (m : model_data (S + W)%s)
           (a : assignation  V m)
           (o : Om V) 
    (o' : Om V)(v : m ** (arm o')) : Type.
  Check (assignation_omit a (o := o)).
  Check ((assignation_comp (S := S)(W2 := _) _ (assignation_omit a (o := o)))).
  refine (
       a o' v = (assignation_comp (S := S) _ (assignation_omit a (o := o))) o' v).
  apply assignation_instantiate.
  assignation (S := S) (V \ o) m.
*)


(* Arguments Op [S V] o . *)
(* Arguments MVar [S V] m . *)

(* Fixpoint msubst {S : signature}{V : msignature} {W : msignature} (f : Om V -> Z S W)(t : Z S V)  { struct t} : W S W *)
(*   := *)
(*   match t with *)
(*     Var n => Var n *)
(*   | Op op v => Op op *)
(*                  (vec_map  *)
(*                     (fun n b => *)
(*                        (b [ derivₙₛ (Var S) Z_ren n f ]ₛ) *)
(*                     ) v) *)
(*   end *)
(*     where "t [ f ]ₘ" := (msubst f t). *)


Definition is_unifier {S : signature}{V : msignature} (t u : T S V) 
           {W}
           {m : model_data (S + W)%s}
             (s : assignation V m) :=
    t [ s ]ₘ = u [ s ]ₘ.

  Definition is_general_unifier {S : signature}{V : msignature} (t u : T S V) { W : msignature }
           {m : model_data (S + W)%s}
             (s : assignation V m) :=
    forall W' (m' : model_data (S + W')%s)
      (s' : assignation V m'), is_unifier t u s' ->
                                    exists (f : model_mor (W ^* m) (W' ^* m')),
                                      forall (w : T S V), 
                                        w [ s' ]ₘ = f (w [ s ]ₘ).
  Section unifier.
    Context {S : signature}.
    Context (eqO : forall (x y : O S), { x = y } + {x <> y}).

    Definition obind (A B:Type) (f:A-> option B) (o : option A) : option B :=
  match o with
    | Some a => f a
    | None => None
  end.


    Record lazy_opt (A : Type) : Type :=
      mk_opt 
      { val : A; valid : bool }.


Record candidate V :=
  mk_candidate
  { cW : msignature;
    cass : assignation V (ZModel (S + cW)%s)
  }.

Arguments cass [V ].

Definition candidate_comp {V}
  (r1 : candidate V)
  (r2 : candidate (cW r1)) : candidate V.
refine {| cW := cW r2 ; cass := _ |}.
generalize (cass r1)(cass r2).
apply assignation_comp.
Defined.

Infix "∘c" := (@candidate_comp _) (at level 30).


Definition id_candidate {V} : candidate V := mk_candidate (id_assignation (m := ZModel (S + V)%s)).
Definition id_candidate_ext {V} (n : nat) : candidate V.
   refine {| cW := V +{ n } |} .
   intros o v.
   unshelve eapply (TMVar ).
   exact (Some o).
   exact v.
   Defined.



Fixpoint vec_fold {A B C : Type}{l : list A}(f : B -> C -> C) (c : C)(v : vec B l) : C :=
  match v with
    NilV => c
  | ConsV _ b lB => vec_fold f (f b c) lB
    end.

Definition vec_fold' {A B C : Type}(f : B -> C -> C)(c : C) :=
  fix rec (l : list A)(v : vec B l) : C :=
  match v with
    NilV => c
  | ConsV _ b lB => f b (rec _ lB)
    end.

Fixpoint vec_fold2 {A B C D : Type}{l : list A}(f : C -> B -> D -> C) (c : C)(v1 : vec B l) {struct v1} :
   vec D l -> C.
  refine (
  match v1 with
    NilV => fun _ => c
  | @ConsV _  _ _ lA b lB =>
      (fun v2 =>
         _
      )
    end).
  set (d := vec_hd v2).
  apply (vec_fold2 A B C D _ f (f c b d) lB).
  apply (vec_tl v2).
  (* revert lB. *)
(*   refine (      match v2 in (vec _ ll) return match ll with nil => IDProp *)
(*                                                        | _ :: ll' => C *)
(*                                               end *)
(*                                               with *)
(*                   NilV => idProp *)
(*                 | ConsV _ d lD => _ *)
(*                                    (* vec_fold2 A B C D _ f (f c b d) lB lD *) *)
(*       end *)
(* ). *)
  Defined.


(*
Equations make_unifier {V}(t u : T S V) : lazy_opt (candidate V) :=
  make_unifier (Var _ n) (Var _ m) := mk_opt id_candidate ( Nat.eqb n m) ;
  make_unifier (Op (SOp o1) v1) (Op (SOp o2) v2) := _;
  make_unifier _ _ := mk_opt id_candidate false.
Next Obligation.
Equations neg (b : bool) : bool :=
neg true := _ ;
neg false := true.
Next Obligation.
*)

Definition lazybind {A B:Type}  (o : lazy_opt A) (f:A-> lazy_opt B) : lazy_opt B :=
  let r := f (val o) in
  {| val := val r; valid := valid r && valid o |}.

Definition retl {A:Type} a : lazy_opt A := {| val := a ; valid := true |}.


Notation "'do' X <- A ; B" := (lazybind A (fun X => B)) (at level 200, X name, A at level 100, B at level 200).

Fixpoint make_unifier {V}(t u : T S V) {struct t }: lazy_opt (candidate V).
  refine 
  (match (t, u) with
     (Var _ n, Var _ m) => mk_opt id_candidate ( Nat.eqb n m)
   | (Op o1 v1, Op o2 v2) => _
   | _ => mk_opt id_candidate false
    end).
  - clear t u.
    revert v1 v2.
    refine (match o1 with
              SOp o1' => match o2 with
                          SOp o2' => _
                        | _ => fun _ _ => mk_opt id_candidate false
                        end
            | _ => fun _ _ => mk_opt id_candidate false
            end
           ).
    refine (if eqO o1' o2' then _ else fun _ _ => mk_opt id_candidate false).
    intro v1.
    refine (match e with eq_refl => _ end).
    unshelve eapply (vec_fold2 _ _ v1).
    (* termination ? *)
    { intros lr t u.
      refine (do r1 <- lr ; _).
      refine (do r2 <- (make_unifier _ (t [ cass r1 ]ₘ) (u [ cass r1 ]ₘ)) ; _).
      apply retl.
      (* intros [[W a] b] t u. *)
      (* set (unif := make_unifier _ (t [ a ]ₘ) (u [ a ]ₘ)). *)
      apply (candidate_comp r2).
      
    }
    exact (retl id_candidate).
    Abort. (* termination !! *)

(* think of unifying t [ c ] and u *)
Fixpoint make_unifier {V }(t : T S V) (c : candidate V) (u : T S (cW c)) {struct t }: lazy_opt (candidate V).
  refine 
  (match (t, u) with
     (Var _ n, Var _ m) => mk_opt id_candidate ( Nat.eqb n m)
   | (Op o1 v1, Op o2 v2) => _
   | _ => mk_opt id_candidate false
    end).
  - clear t u.
    revert v1 v2.
    refine (match o1 with
              SOp o1' => match o2 with
                          SOp o2' => _
                        | _ => fun _ _ => mk_opt id_candidate false
                        end
            | _ => fun _ _ => mk_opt id_candidate false
            end
           ).
    refine (if eqO o1' o2' then _ else fun _ _ => mk_opt id_candidate false).
    intro v1.
    refine (match e with eq_refl => _ end).
    unshelve eapply (vec_fold2 _ _ v1).
    (* termination ? *)
    { intros lr t u.
      refine (do r1 <- lr ; _).
      unshelve refine (do r2 <- (make_unifier _ t (* [ cass r1 ]ₘ *) _ _ (*(u [ cass r1 ]ₘ) *)) ;
                 (* retl (candidate_comp r2) *)
                 _
             ).
      +
      apply retl.
      (* intros [[W a] b] t u. *)
      (* set (unif := make_unifier _ (t [ a ]ₘ) (u [ a ]ₘ)). *)

      (*
      apply (candidate_comp r2).
      
    }
    exact (retl id_candidate).
*)
      Abort.


(*
Fixpoint in_mvar {S V} ov (t : T S V) {struct t} : Prop :=
  match t with
    Var _ _ => False
  | Op (SMVar o) v => vec_fold (fun x p => x \/ p) (o = ov) (vec_map (fun _ => in_mvar ov) v)
  | Op (SOp o) v =>  vec_fold (fun x p => x \/ p) False (vec_map (fun _ => in_mvar ov) v)
    end.

*)
(*
Open Scope bool_scope.
Fixpoint notin_mvar {S V} ov (t : T S V) {struct t} : bool :=
  match t with
    Var _ _ => true
  | Op (SMVar o) v => (o <>m ov) && (vec_fold' (fun x p => notin_mvar ov x && p) true v)
  | Op (SOp o) v => vec_fold' (fun x p => notin_mvar ov x && p) true v
    end.
*)

Inductive Notin_mvar {S V} (ov : Om V) : T S V -> Type :=
  NMvar : forall n, Notin_mvar  ov (Var _ n)
| NMsop : forall (o : O S) (v : vec (T S V) (ar o)), Notin_mvar_vec ov v ->
                                                  Notin_mvar ov (TOp v)
| NMmvar : forall (o : Om V) (eqo : o <> ov) (v : (T S V) ** (arm o)), Notin_mvar_vec ov v ->
                                                  Notin_mvar ov (TMVar v)
with Notin_mvar_vec {S V} (ov : Om V) : forall (l : list nat), vec (T S V) l -> Type :=
| NMNilV : Notin_mvar_vec ov NilV
| NMConsV : forall a b l v, Notin_mvar_vec ov v -> Notin_mvar ov b -> Notin_mvar_vec ov (ConsV a (lA := l) b v).


(*
Fixpoint in_mvar {S V} ov (t : T S V) {struct t} : Prop :=
  match t with
    Var _ _ => False
  | Op (SMVar o) v => vec_fold (fun x p => in_mvar ov x \/ p) (o = ov) v
  | Op (SOp o) v =>  vec_fold (fun x p => in_mvar ov x \/ p) False v
    end.
*)
              




Fixpoint remove_mvar {V} (t : T S V) ov (h : Notin_mvar ov t) { struct h }: T S (V \ ov)
with remove_mvar_vec {V}(l : list nat)(v : vec (T S V) l) ov (h : Notin_mvar_vec ov v) {struct h} : vec (T S (V \ ov)) l.
  {
    destruct h.
    - exact (Var _ n).
    - apply (TOp (o := o)).
      eapply remove_mvar_vec.
      eassumption.
    - unshelve eapply (TMVar (V := V \ ov)(o := exist _ o _)); cbn.
      {
        apply neq_negb_deceq.
        assumption.
      }
      eapply remove_mvar_vec.
      eassumption.
  }
  {
    destruct h.
    { constructor. }
    constructor.
    - eapply remove_mvar.
      eassumption.
    - eapply remove_mvar_vec.
      eassumption.
  }
Defined.

Lemma remove_mvar_vec_assignation_incl 
       {V}(l : list nat)(v : vec (T S V) l) ov (h : Notin_mvar_vec ov v) : 
   vec_map (fun _ x => x [ assignation_incl (o := ov) (m := Z_model_data _)]ₘ) (remove_mvar_vec h) = v. 
  Admitted.

Lemma Notin_mvar_op {V}  (o : O S) ov v (t := (Op (S := S + V)%s (SOp (V := V) o) v))(h : Notin_mvar ov t) :
  Notin_mvar_vec ov v.
  Admitted.

(*
Lemma Notin_mvar_irrelevant   {V : msignature}(o :  Om V) (t : T S V)(h h' : Notin_mvar o t) :
  h = h'.
  Admitted.
*)
Lemma Notin_mvar_op_eta {V}  (o : O S) ov v (t := (Op (S := S + V)%s (SOp (V := V) o) v))(h : Notin_mvar ov t) :
  h = NMsop (Notin_mvar_op h).
  Admitted.



Lemma remove_mvar_op {V}  (o : O S) ov v (t := (Op (S := S + V)%s (SOp (V := V) o) v))(h : Notin_mvar ov t)
      : remove_mvar h = Op (S := S + _)%s (SOp (V := _) o) (remove_mvar_vec (Notin_mvar_op h)).
  assert (heq := Notin_mvar_op_eta h).
  rewrite heq at 1.
  cbn.
  reflexivity.
Qed.

(*
Fixpoint remove_mvar {V} (t : T S V) { struct t} : forall o' (h : notin_mvar o' t), T S (V \ o').
  refine (
      match t with
        Var _ n => fun _ _ => Var _ n
      | Op o v =>
          match o with
            SOp o => fun v o' => _
          | SMVar o => fun v o' => _
          end v
      end
    ).
  - cbn.
    intro h.
    apply (TOp (V := V \ o' ) (o := o)).
    revert h.
     revert v.
     cbn.
     generalize (ar o).
    refine (fix rec_vec_mvar l v {struct v} := _) .
    refine (
        match v with
          NilV => _
        | ConsV a b v => _
        end
      ).
    + cbn.
      constructor.
    + cbn.
      intro h.
      constructor.
      * apply (remove_mvar _ b).
        cbn in h.
        eapply Bool.andb_prop_elim in h.
        destruct h; assumption.
      * specialize (rec_vec_mvar _ v).
        apply rec_vec_mvar.
        eapply Bool.andb_prop_elim in h.
        destruct h; assumption.
  - cbn.
    intro h.
    apply Bool.andb_prop_elim in h.
    assert (h1 := proj1 h).
    assert (h2 := proj2 h).
    clear h.
    unshelve eset (o'' := exist _ o h1 : O (V \ o') ).

    apply (TMVar (V := V \ o' ) (o := o'')).
    cbn.
    clear o'' h1.
    revert h2.
     revert v.
     cbn.
     generalize (arm o).
     intro n.
     generalize (List.repeat 0 n) as ar.
     (* remember (List.repeat 0 n) as ar eqn:eq_ar. *)
     intro v.
     revert (* ar *) v (* n  *)(* eq_ar *).
         refine (fix rec_vec l v {struct v} := _) .
    refine (
        match v with
          NilV => _
        | ConsV a b v => _
        end
      ).
    { constructor. }
    intros (* n eqn *) h.
    cbn in h.
    eapply Bool.andb_prop_elim in h.
    assert (h1 := proj1 h).
    assert (h2 := proj2 h).
    clear h.
    constructor.
    * apply (remove_mvar _ b).
      exact h1.
    * eapply rec_vec.
      exact h2.
Defined.
*)





Definition candidate_instantiate {V} {o : Om V}(a : T S (V \ o)) : candidate V.
 refine  {| cW := V \ o; cass := _|}.
 apply assignation_instantiate.
 exact a.
Defined.

Definition msignature_replace (V : msignature)(ov : Om V) (n : nat) : msignature :=
  {| Om := Om V; arm := fun o => if o =m ov then n else arm o |}.

Notation "V [ o := n ]" := (@msignature_replace V o n) (at level 30).

Definition replaced_vec {V : msignature}(ov : Om V)(n : nat){B}(v : B ** n) :
  ( B ** (arm (m := V [ ov := n])ov)).
Proof.
  cbn.
  destruct (ov =m ov).
  exact v.
  contradiction.
Defined.


Definition TMVar_replaced {V : msignature}(ov : Om V)(n : nat)(v : (T S (V [ ov := n ])) ** n) :
  T S (V [ ov := n]).
  apply (TMVar (V := V [ ov := n])(o := ov)).
  apply replaced_vec.
  exact v.
Defined.


Lemma replaced_vec_vec_map {V : msignature}(ov : Om V)(n : nat)
      (* (v : (T S (V [ ov := n ])) ** n) *)
      {B}
      (v : B ** n)
      (f : nat -> B -> (T S (V [ ov := n ]))) :
  replaced_vec ov (vec_map f v) = vec_map f (replaced_vec ov v).
Proof.
  unfold replaced_vec.
  cbn.
  destruct (ov =m ov).
  reflexivity.
  contradiction.
Defined.

Definition assignation_replace
  {V : msignature}
  (o : Om V)
  (n : nat)
  (a : T S (V [ o := n ]))
  : assignation V (ZModel (S + V [ o := n ])%s).
 intro o'.
 cbn.
 generalize (TMVar (S := S)(V := V [ o := n]) (o := o')).
 cbn.
 destruct (o' =m o).
 - intro.
   eapply mk_an_assignation.
   exact a.
 - intro h.
   exact h. 
   Defined.

(* other method, with rewrite *)
(*
Definition assignation_replace
  {V : msignature}
  (o : Om V)
  (n : nat)
  (a : T S (V [ o := n ]))
  : assignation V (ZModel (S + V [ o := n ])%s).
 intro o'.
 cbn.
 (*
 generalize (TMVar (S := S)(V := V [ o := n]) (o := o')).
*)
 cbn.
 destruct (o' =m o).
 - intro.
   eapply mk_an_assignation.
   exact a.
   eassumption.
 - (*intro h.
   exact h. *)
   cbn.
   hnf.
   intro v.
   eapply (TMVar(V := V [ o := n])(o := o')).
   cbn.
   rewrite (neq_negb_deceq_false n0).
   exact v.
   Defined.
*)


Definition candidate_replace {V} {o : Om V}(n : nat)(a : T S (V [ o := n ])) : candidate V.
 refine  {| cW := V [ o := n]; cass := _|}.
 eapply (assignation_replace).
 exact a.
Defined.

(*
Definition assignation_replace'
  {V : msignature}
  (o : Om V)
  (n : nat)
  (a : T S (V +{ n } \ Some o ))
  : assignation V (ZModel (S + (V +{ n } \ Some o ))%s).
 intro o'.
 cbn.
 eapply candidate_instantiate.
 generalize (TMVar (S := S)(V := (V \ o +{ n } ) ) ).
 cbn.
 destruct (o' =m o).
 - intro.
   eapply mk_an_assignation.
   exact a.
 - intro h.
   exact h. 
   Defined.
*)


Definition candidate_replace' {V} {o : Om V}(n : nat)(a : T S ((V +{n} \ Some o) )) : candidate V.
  unshelve refine (_ ∘c _).
  apply id_candidate_ext.
  exact n.
  cbn.
  eapply candidate_instantiate.
  exact a.
Defined.

Definition TMVar_replaced' {V : msignature}(ov : Om V)(n : nat)(v : (T S (V +{ n } \ Some ov)) ** n) :
  T S (V +{ n } \ Some ov).
  unshelve refine (TMVar (V := V +{ n } \ Some ov)(o :=  exist _ None _) _).
  - cbn.
    easy.
  - cbn.
    exact v.
Defined.

Fixpoint Notin_mvar_msubst {V}{ov : Om V} t u (ht : Notin_mvar ov t) {struct ht}:
  t [assignation_instantiate u ]ₘ = remove_mvar ht
with Notin_mvar_vec_msubst {V}{ov : Om V} l (v : vec _ l) u (hv : Notin_mvar_vec ov v) {struct hv}:
  vec_map (fun _ : nat => msubst' (assignation_instantiate u)) v = remove_mvar_vec hv.
{
  destruct ht.
  reflexivity.
  - cbn.
    f_equal.
    apply Notin_mvar_vec_msubst.
  - cbn.
    unfold assignation_instantiate at 1.
    (*
    Check (fun p =>  match
    p as s
    return
      ((negb s -> T S (V \ ov) ** arm o -> T S (V \ ov)) -> an_assignation (arm o) (Z_model_data (S + V \ ov)%s))
  with
  | left a => fun _ : negb (left a) -> T S (V \ ov) ** arm o -> T S (V \ ov) => mk_an_assignation (m := Z_model_data _) u
  | right _ => fun h : true -> T S (V \ ov) ** arm o -> T S (V \ ov) => h eq_refl
  end (fun P : o <>m ov => TMVar (V := V \ ov)(o:=exist (fun v0 : Om V => v0 <>m ov) o P))
    (vec_map (fun _ : nat => msubst' (assignation_instantiate u)) v) =
  Op (S := S + V \ ov)%s (SMVar (V := V \ ov) (exist (fun v0 : Om V => v0 <>m ov) o (neq_negb_deceq eqo))) (remove_mvar_vec n)
).
    Check (  match
    o =m ov as s
    return
      ((negb s -> T S (V \ ov) ** arm o -> T S (V \ ov)) -> an_assignation (arm o) (Z_model_data (S + V \ ov)%s))
  with
  | left a => fun _ : negb (left a) -> T S (V \ ov) ** arm o -> T S (V \ ov) => mk_an_assignation (m := Z_model_data _) u
  | right _ => fun h : true -> T S (V \ ov) ** arm o -> T S (V \ ov) => h eq_refl
  end (fun P : o <>m ov => TMVar (V := V \ ov)(o:=exist (fun v0 : Om V => v0 <>m ov) o P))
    (vec_map (fun _ : nat => msubst' (assignation_instantiate u)) v) =
  Op (S := S + V \ ov)%s (SMVar (V := V \ ov) (exist (fun v0 : Om V => v0 <>m ov) o (neq_negb_deceq eqo))) (remove_mvar_vec n)
).
    etransitivity.
    pattern (o =m ov).
    destruct (o =m ov).
    refine (match o =m ov with left p => _ | right p => _ end).
*)
    unfold assignation_instantiate at 1.
    destruct (o =m ov) at 1.
    contradiction.
    cbn.
    assert (irr : neq_negb_deceq n0 = neq_negb_deceq eqo) by apply irrelevance_bool.
    rewrite irr.
    f_equal.
    apply Notin_mvar_vec_msubst.
}
{
  destruct hv.
  - reflexivity.
  - cbn.
    f_equal.
    apply Notin_mvar_msubst.
    apply Notin_mvar_vec_msubst.
}
Qed.
(*
Fixpoint notin_mvar_msubst {V}{r : Om V}t u (ht : notin_mvar r t) {struct t}:
 t [assignation_instantiate u ]ₘ = remove_mvar ht.
  destruct t.
  reflexivity.
  destruct o.
  - cbn -[remove_mvar].
    cbn.
    cbn in ht.
    f_equal.
    revert v ht.
    cbn.
    generalize (ar o).
    refine (fix rec_vec l v {struct v} := _) .
    destruct v.
    reflexivity.
    cbn.
    intro ht.
    f_equal.
    + apply notin_mvar_msubst.
    + apply rec_vec.
  - cbn.
    cbn in ht.
    generalize ( Bool.andb_prop_elim _ _ ht).
    clear ht.
    intros [ht1 ht2].
    cbn.
    unfold assignation_instantiate.
    set (eo := o =m r).
    unfold eo at 1.
    destruct (o =m r) at 1.
    {
      exfalso.
      revert ht1.
      destruct (o =m r); easy.
    }
    cbn.
    assert (e : neq_negb_deceq n = ht1) by apply irrelevance_bool.
    rewrite e.
    clear e.
    cbn.
    f_equal.
    Guarded.
    clear eo n ht1.
    revert v ht2.
    cbn.
    generalize (arm o).
    intro n.
    generalize (List.repeat 0 n) as ar.
    refine (fix rec_vec l v {struct v} := _) .
    destruct v.
    reflexivity.
    cbn.
    intro h.
    f_equal.
    + apply notin_mvar_msubst.
    + apply rec_vec.
Qed.
*)
Lemma assignation_comp_msubst'
 {V W1 W2 : msignature} {m : model_data (S + W2)%s}
  (a : assignation V (ZModel (S + W1)%s)) (a' : assignation W1 m) t :
  t [ a ]ₘ [ a' ]ₘ =
  t [ a ∘a a' ]ₘ. 
  Admitted.

(*
M[x1, ..., xn]
Je veux que m(x1,..,xn) soit de la forme N[0,...,m]
        donc m(t1,..,tn) = N[.., ti, ..] ou ti est a la position xi.
hmm, c'est louche car m(t1,..,tn) as des termes ouverts,
donc ca ne peut pas etre un morphisme de modules..
Autre maniere: je veux que m[i ↦ xi] = N[0,..,m]
introduce new metavar N
M[x1,...,xn] ↦ N[0,.., max(xn)-1] 
donc
M[t1,..,tn] = N[0,..,ti, ..]
Je cherche t tel que
  M[t1, ..,tn] = t[xi ↦ ti]
et M[x1, ..,xn] = t [ xi↦xi]
il faut mettre les ti la ou il y avait les xi
*)
(*
Definition normalise_mvar_vec {V} (o : Om V)(n := arm o)(v : nat ** n)(W :=
                                      {| Om := Om V;
                arm := fun o' => if o =m o' then vec_max v else arm o'
                                      |})
             :
  assignation V (Z_model_data (S + W)%s).
  intro o'.
  hnf.
  cbn.
  intro v'.
  apply (TMVar (V := W)(o := o')).
  cbn.
  destruct (o =m o').
  Cane peut pas marcher
  - exact (vec_mk 0 (fun x _ => Var _ x) (List.repeat 0 _)).
  - exact v'.
  refine (if o =m o' then _ else _ ).
  - apply 
  Admitted.
*)
(*
                     (c' := {| cW := {| Om := Om V;
                                       arm := fun o' => if o =m o' then arm o' else arm o'
                                     |} ;
                     cass := fun o' => if o =m o' then TMVar (o := o') else TMVar (o := o') 
                     |}),
*)

Fixpoint inverse_vec {A}{l : list A} (p : nat)(v : vec nat l ) : (nat -> nat).
  refine (
  match v with
    NilV => fun n => n
  | ConsV a b v => _
  end).
  - intro n.
    refine (if n =m b then p else inverse_vec _ _ (1 + p) v n).
Defined.
 
Notation "x ̅ ¹" := (inverse_vec 0 x) (at level 0).

Inductive Vec_In (A B : Type) (b : B) : forall (l : list A), vec B l -> Prop :=
  InV_hd : forall a (l :list A) v, @Vec_In A B b _ (ConsV a (lA := l) b v)
| InV_tl : forall a b' l v, @Vec_In A B b _ v -> @Vec_In A B b _ (ConsV a (lA := l) b' v).

Open Scope bool_scope.
(* Maybe I only need an inversion on Vec_In Cons ? *)
Fixpoint vec_in (A B : Type){eqb : EqDec B} (b : B) (l : list A)(v : vec B l) : bool :=
  match v with
    NilV => false
  | ConsV a b' v => (b =m b') || vec_in b v
    end.


Lemma Vec_In_in 
      (A B : Type){eqb : EqDec B} (b : B) (l : list A)(v : vec B l) : vec_in b v <-> Vec_In b v.
Admitted.


Fixpoint inverse_vec_value {A : Type}(l : list A)(v : vec nat l) p n (hn : Vec_In n v) {struct hn} :
  inverse_vec p v n = p + inverse_vec 0 v n.
Proof.
  destruct hn.
  - cbn.
    destruct (n =m n); [|congruence].
    lia.
  - cbn.
    destruct (n=m b').
    + lia.
    + etransitivity.
      * apply inverse_vec_value.
        assumption.
      * cbn.
        etransitivity; revgoals.
        rewrite inverse_vec_value ; [|assumption].
        reflexivity.
        lia.
Qed.

Fixpoint inverse_vec_is_inverse {A : Type}(l : list A)(v : vec nat l) b n (hn : Vec_In n v) {struct hn} :
      vec_nth b v ((v) ̅ ¹ n) = n.
destruct hn.
- cbn.
  destruct (n =m n).
  + reflexivity.
  + lia.
- cbn.
  destruct (n =m b').
  lia.
 rewrite inverse_vec_value by assumption.
 cbn.
 apply inverse_vec_is_inverse.
 assumption.
 Qed.

Lemma vec_hd_tl_eta {A}{B}{a : A}{lA} (v : vec B (a :: lA)) : v = ConsV a (vec_hd v)  (vec_tl v).
  Admitted.
Lemma vec_map_ext_In {A B C} (f g :  B -> C)(l : list A)(v : vec B l)
      (eq_fg : forall (b : B), Vec_In b v -> f b = g b) :
  vec_map (fun _ => f) v =
  vec_map (fun _ => g) v.
  Admitted.
Fixpoint distinct (A B : Type){eqb : EqDec B} (l : list A)(v : vec B l) : bool :=
  match v with
    NilV => true
  | ConsV a b' v => (negb (vec_in b' v)) && distinct v
    end.
(* TODO: see if this can be used instead of the previous lemma *)
Fixpoint map_inverse_vec_mk {A B : Type}(l : list A)(f : nat -> B)(v : vec nat l) (d : distinct v) {struct v} :
      vec_map (fun _ x => f (inverse_vec 0 v x)) v = vec_mk 0 (fun n _ => f n) l.
 destruct v.
- cbn.
  reflexivity.
- cbn.
  rewrite refl_deceq_true.
  f_equal.
  cbn.
  cbn in d.
  apply andb_prop in d.
  destruct d as [d1 d2].
  rewrite vec_mk_eqf.
  cbn.
  etransitivity; revgoals.
  apply (map_inverse_vec_mk _ _ _ _ v d2).
  apply vec_map_ext_In.
  intros b inb.
  destruct (b =m n).
  + exfalso.
    subst b.
    rewrite <- Vec_In_in in inb.
    rewrite inb in d1.
    cbn in d1.
    discriminate d1.
  + rewrite inverse_vec_value.
    reflexivity.
    exact inb.
Qed.
Fixpoint inverse_vec_lt {A : Type }{l : list A} (v : vec nat l) (n : nat) (inn : Vec_In n v) {struct inn }:
  v ̅ ¹ n < length l.
Proof.
  destruct inn.
  - cbn.
    rewrite refl_deceq_true.
    lia.
  - cbn.
    destruct (n =m b').
    lia.
    rewrite inverse_vec_value;[|assumption].
    cbn.
    apply lt_n_S.
    apply inverse_vec_lt.
    assumption.
Qed.

Fixpoint vec_nth_default {A B : Type} (b b' :B) (l : list A) (v :  vec B l) (n : nat) {struct v} :
  n < length l ->
  vec_nth b v n = vec_nth b' v n.
Proof.
  destruct v.
  - cbn.
    lia.
  - cbn.
    destruct n.
    + reflexivity.
    + intro.
      apply vec_nth_default.
      lia.
Qed.

Corollary inverse_vec_is_inverse2 {A B : Type}(l : list A)(v : vec nat l)(v' : vec B l) (d : distinct v) b :
      vec_map (fun _ x => vec_nth (b x) v' (inverse_vec 0 v x)) v = v'.
  destruct l.
  - 
    refine (match v' with NilV => _ end).
    refine (match v with NilV => _ end).
    reflexivity.
  - set (n0 := vec_hd v).
    enough ( h : vec_map (fun (_ : A) (x : nat) => vec_nth (b x) v' ((v) ̅ ¹ x)) v
           = vec_map (fun (_ : A) (x : nat) => vec_nth (b n0) v' ((v) ̅ ¹ x)) v).
    {
      etransitivity.
      apply h.
      etransitivity.
      eapply (map_inverse_vec_mk _ (v := v) d).
      apply vec_mk_nth0.
    }
    apply vec_map_ext_In.
    intros b' inb'.
    apply vec_nth_default.
    apply inverse_vec_lt.
    assumption.
  Qed.

Fixpoint vec_nth_map {A B C} (l : list A)(v : vec B l)(f : A -> B -> C)p (hp : p < length l) a b c {struct v}: 
  vec_nth c (vec_map f v) p = f (List.nth p l a) (vec_nth b v p).
  revert hp.
  refine (
  match v with
    NilV => _
  | @ConsV _ _ a l b v => _
  end).
  - cbn.
    lia.
  - cbn.
    destruct p.
    reflexivity.
    cbn.
    intro hp.
    apply vec_nth_map.
    apply lt_S_n.
    assumption.

    Qed.
Fixpoint vec_nth_map' {A B C} (l : list A)(v : vec B l)(f : A -> B -> C)p a b c {struct v}: 
   f a b = c ->
  vec_nth c (vec_map f v) p = f (List.nth p l a) (vec_nth b v p).
  refine (
  match v with
    NilV => _
  | @ConsV _ _ a l b v => _
  end).
  - cbn.
    destruct p; congruence.
  - cbn.
    destruct p.
    reflexivity.
    cbn.
    intro hp.
    apply vec_nth_map'.
    assumption.
    Qed.
Lemma vec_nth_map'' {A B C} (l : list A)(v : vec B l)(f : A -> B -> C)p a b  : 
  vec_nth (f a b) (vec_map f v) p = f (List.nth p l a) (vec_nth b v p).
  apply vec_nth_map'.
  reflexivity.
    Qed.

(*
Fixpoint vec_inverse_is_inverse {A} (l : list A) (v : vec nat l) p q (hp : p < length l) (d : _) {struct v} :
    vec_nth d v (inverse_vec q v p) = (p - q).
  Proof.
    revert p q hp.
  refine (
  match v with
    NilV => _
  | @ConsV _ _ a l b v => _
  end).
  cbn.
      lia.
    - intros.
      cbn -[vec_nth].
      destruct (p =m q).
      + destruct b.
        * cbn.
          f_equal.
          lia.
        * specialize (vec_inverse_is_inverse _ l v).
          cbn.
          apply vec_inverse_is_inverse.
          unfold vec_to_ren in vec_inverse_is_inverse.
          apply vec_inverse_is_inverse.
          rewrite IHv.

    Abort.
*)

Lemma In_fv_remove_mvar1 {V} ov (u : T S V)(hu : Notin_mvar ov u) p :
  In_fv p (remove_mvar hu) -> In_fv p u.
Admitted.

(*
vec_common_pos v0 v1 v1' means
that v0 is the vector of common positions between v1 and v1'
 *)
Inductive vec_common_pos {B} : forall (n0 : nat) (v0 : B ** n0) (n1 : nat)(v1 v1': B ** n1) , Type
  :=
  CPNil : @vec_common_pos B 0 NilV 0 NilV NilV
| CPIn : forall b n0 v0 n1 v1 v1', @vec_common_pos B n0 v0 n1 v1 v1' ->
                                @vec_common_pos B (1 + n0)(ConsV 0 b v0)(1 + n1)(ConsV 0 b v1)(ConsV 0 b v1')
| CPNotIn : forall b b' n0 v0 n1 v1 v1', @vec_common_pos B n0 v0 n1 v1 v1' ->
                                      b <> b' ->
                                vec_common_pos v0 (n1 := 1 + n1)(ConsV 0 b v1)(ConsV 0 b' v1')


.
Inductive vec_common_val {B}{n1}(v1 : B ** n1) : forall  n1' (v1': B ** n1') (n0 : nat) (v0 : B ** n0), Type
  :=
  CVNil : @vec_common_val B n1 v1 0 NilV 0 NilV
| CVIn : forall n0 (v0 : B ** n0) n1' (v1' : B ** n1') b,
    vec_common_val v1 v0 v1' ->
    Vec_In b v1 -> vec_common_val v1 (n1' := 1 + n1')(ConsV 0 b v1')(n0 := 1 + n0) (ConsV 0 b v0) 
| CVNotIn : forall n0 (v0 : B ** n0) n1' (v1' : B ** n1') b,
    vec_common_val v1 v0 v1' ->
    ~ Vec_In b v1 -> vec_common_val v1 (n1' := 1 + n1')(ConsV 0 b v1') v0. 

Lemma vec_common_pos_val {B}{n0}(v0 : B ** n0) {n1}( v1 v1' : B ** n1) :
  vec_common_pos v0 v1 v1' -> vec_common_val v1 v1' v0.
  Admitted.

(*
Definition replace_mvar {V} (o : Om V)(n := arm o)(v : nat ** n)(W :=
                                      {| Om := Om V;
                arm := fun o' => if o =m o' then vec_max v else arm o'
                                      |})
             :
  assignation V (Z_model_data (S + W)%s).
  intro o'.
  hnf.
  cbn.
  intro v'.
  apply (TMVar (V := W)(o := o')).

  destruct (o =m o').
  Cane peut pas marcher
  - exact (vec_mk 0 (fun x _ => Var _ x) (List.repeat 0 _)).
  - exact v'.
  refine (if o =m o' then _ else _ ).
  - apply 
  Admitted.
*)

(* ************



This version that follows mac bride (in that it outputs a candidate V rather than candidate (acc V))
is harder to prove correct for the vector cons case!
Indeed, I now that t unifies with u with output s, then
I now that vector v1 unifies with v2 with output s' (input s), but then I don't know
why s' still unifies t and u !! Whereas in the candidate (acc V) case, s' would be explicitly
a composition with s.

I would need to prove something before, like if the input unifies things, then the output
also does.

 ************* *)
Lemma neq_Some {A}{o1 o2 : A} (eo : o1 <> o2) : Some o2 <> Some o1.
  congruence.
Qed.

(*
Lemma neq_Some_eq_dec {A} {eqA : EqDec A}{o1 o2 : A} (eo : o1 <> o2) : (Some o2 =m Some o1) = right (neq_Some eo).
Admitted.
*)
(*

Goal forall V n0 o1 o2 (eo : o1 <> o2), (fun v : Om (V +{ n0}) => is_true (v <>m Some o1)) (Some o2).
intros.
cbn beta.
apply neq_negb_deceq.
apply Some_neq.
right.
eapply right.
cbn.
*)


(* thanks to applyass_spec,
   we can always assume that the input is the identity *)
Inductive unifier_spec  : forall V, T S V -> T S V -> forall (acc : candidate V) , candidate V -> Prop :=
  var_spec : forall V n c, @unifier_spec V (Var _ n) (Var _ n) c c
| sop_spec : forall V o v1 v2 c1 c2,
    @unifier_spec_vec V _ v1 v2 c1 c2
    ->
    @unifier_spec V (Op (S := S + V)%s (SOp o) v1) (Op (S := S + V)%s (SOp o) v2) c1 c2
| same_mvar : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) 
                n0 v0, vec_common_pos (n0 := n0) v0 v1 v2 ->
                       distinct v1 -> distinct v2 ->
                       @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                                     id_candidate
                                     (candidate_replace' (o := o)
                                                (TMVar_replaced' (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ))
| different_mvar : forall V o1 o2 (neq_o12 : o1 <> o2)(v1 : vec nat (ar (s := S + V)%s(SMVar o1)))
                     (v2 : vec nat (ar (s := S + V)%s(SMVar o2)))
                     n0 v0
                    (o2' := exist _ (Some o2) (neq_negb_deceq (neq_Some neq_o12)) : Om (V +{ n0 } \ Some o1))
               , vec_common_val (n0 := n0) v1 v2 v0 ->
                       (* distinct v1 -> distinct v2 -> *)
                       @unifier_spec V (Op (S := S + V)%s (SMVar o1) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o2) (vec_map (fun _ => Var _)v2))
                                     id_candidate
                                     (
                                       id_candidate_ext n0
                                        ∘c candidate_instantiate (V := V +{ n0 }) (o := Some o1)
                                          (TMVar (V := V +{ n0 } \ Some o1)(o := exist _ None eq_refl)
                                                (vec_map (fun _ p => Var _ (v1 ̅ ¹ p)) v0))
                                        ∘c candidate_instantiate (V := V +{ n0 } \ Some o1)
                                          (o := o2') 
                                          (TMVar (V := V +{ n0 } \ Some o1 \ o2')(o := exist _ (exist _ None eq_refl) eq_refl)
                                          (vec_map (fun _ p => Var _ (v2 ̅ ¹ p)) v0))
                                     )
                                     
                                     (* (candidate_comp (r1 :=  *)
                                     
                                     (* candidate_replace (o := o1) *)
                                     (*            (TMVar_replaced (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ)) *)
                                     (* (candidate_instantiate (o := o2) _) *)
                                     (* ) *)

(*
1. m1[x1,..,xn] = m1[y1,..,yn]
  m1 ↦ m3 whose arity the subset where xi = yi
  m1[x1,..,xn] ↦ m3[]

2. m1[x1,..,xn] = m2[y1,..,ym]
  m1,m2 ↦ m3 whose arity the common intersection {x1,..,xn} ∩ {y1,..,ym}

When metavariables are different, you can reorder those parameters in 2. but not in 1.
 *)



| applyass_spec : forall V t u c cf, @unifier_spec _ (t [ cass c ]ₘ) (u [ cass c ]ₘ) id_candidate cf
                                            -> 
                                              @unifier_spec V t u c (c ∘c cf)
(* M[k1,...,kₙ] = t
then M [u1,...,uₙ] = t [kᵢ ↦ uᵢ]
Let us assume to start with that k1,...,kn = 0,..,n-1
and maybe add an instantiation case that replace M[k1, ..., kn] with N[0,..,m]?
 *)
   (* ce qu il faut faire c'est construire un inverse (en tant que nat -> nat) de v (vecteur d'entiers) *)
   (* et ensuite mk_assignation de t[v^-1] *)
| instantiation_spec : forall V (c0 := id_candidate) o (n := arm o) (v : nat ** n)(* (v : nat ** arm o) *) (u : T S V)
                         (hu : Notin_mvar o u)
  (hufv : forall n, In_fv n u -> Vec_In n v), (* next_fv u <= n *)
                          @unifier_spec V
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _) v))
                                            u
                                            c0
                                            (candidate_instantiate (remove_mvar hu [ fun k =>  Var _ (v ̅ ¹ k) ]ₛ))
                                            (* (mk_assignation (m := ZModel (S + V \ o)) ) *)
                                                           (* missing case: instantiation *)
| sym_spec : forall V c0 t u c, @unifier_spec V t u c0 c -> unifier_spec u t c0 c
(* Inductive unifier_spec  : forall V, T S V -> T S V -> forall (acc : candidate V) , candidate V -> Prop := *)

with unifier_spec_vec : forall V (l : list nat), vec (T S V) l -> vec (T S V) l -> forall c : candidate V, candidate V -> Prop :=
  NilV_spec : forall V c, @unifier_spec_vec V _ NilV NilV c c
| ConsV_spec : forall V n l t1 t2 (v1 v2 : vec (T S V) l) c1  c1' c2, 
                                                          (* do we need to take n into account? I think n *)
                                        @unifier_spec_vec V _ v1 v2 c1 c1' ->
                                        @unifier_spec V t1 t2 c1' c2 ->
                                        @unifier_spec_vec V _ (ConsV n t1 v1) (ConsV n t2 v2) c1
                                                         c2.

(*
Lemma vec_common_pos_subst n1
  (v1, v2 : nat ** n1)
  (n0 : nat)
  (v0 : nat ** n0)
  (commonPos : vec_common_pos v0 v1 v2)
  :
  vec_map (fun _ b : nat => Var (S + V [o := n0])%s b) v1 = vec_map (fun _ b : nat => Var (S + V [o := n0])%s b) v2
*)
Lemma assignation_replace_TMVar_replaced
  {V : msignature}
  (o : Om V)
  (n : nat)
  (a : T S (V [ o := n ]))
  (v : T S (V [ o := n ]) ** (arm o))
  
  : assignation_replace a v =
      a [ vec_to_ren (m := Z_model_data _) v].
  unfold assignation_replace.
  generalize (TMVar (S := S)(V := V[o := n])(o:=o)).
  cbn.
  destruct (o =m o).
  reflexivity.
  contradiction.
Qed.

(*
Lemma assignation_replace'_TMVar_replaced'
  {V : msignature}
  (o : Om V)
  (n : nat)
  (a : T S (V [ o := n ]))
  (v : T S (V [ o := n ]) ** (arm o))
  
  : assignation_replace' a v =
      a [ vec_to_ren (m := Z_model_data _) v].
  unfold assignation_replace.
  generalize (TMVar (S := S)(V := V[o := n])(o:=o)).
  cbn.
  destruct (o =m o).
  reflexivity.
  contradiction.
Qed.
*)

(*
Inductive Vec_In' (A B : Type) (a : A)(b : B) : forall (l : list A), vec B l -> Prop :=
  InV_hd' : forall (l :list A) v, @Vec_In' A B a b _ (ConsV a (lA := l) b v)
| InV_tl' : forall a' b' l v, @Vec_In' A B a b _ v -> @Vec_In' A B _ b  _ (ConsV a' (lA := l) b' v).

Lemma vec_map_ext_In' {A B C} (f g : A -> B -> C)(l : list A)(v : vec B l)
      (eq_fg : forall (a : A)(b : B), Vec_In' a b v -> f a b = g a b) :
  vec_map f v =
  vec_map g v.
  Admitted.
*)

     (* M(0,1,2,4) M(2,1,0,4)
v0 = [1, 4]
v0 ^-1 : 1 ↦ 0
         4 ↦ 1

v1 ^-1 : 1 ↦ 1
         4 ↦ 3
  m(x,y,z,t) = N(y,t)
             = N(1,4)(1 ↦ 0, 4 ↦ 1)[x,y,z,t]
             = N(0,1)[.] = N(x,y)
non
             = N(1,4)(1 ↦ 1, 4 ↦ 3)(0 ↦ y, 1 ↦ t)

l.h.s [0, 1]

a = N(1,3)


      
     *)
Lemma vec_map_nth_common_pos x n0 v0 n1 v1 v1'
  (commonPos : @vec_common_pos _ n0 v0 n1 v1 v1') :
    vec_map (fun _ b : nat => (vec_nth x v1 ((v0) ̅ ¹ b))) v0 =
      vec_map (fun _ b : nat => (vec_nth x v1' ((v0) ̅ ¹ b))) v0.
  induction commonPos.
  - reflexivity.
  - cbn.
    f_equal.
    + rewrite refl_deceq_true.
      reflexivity.
    + apply vec_map_ext_In.
      intros y iny.
      rewrite 2!(inverse_vec_value _ iny).
      cbn.
      destruct (_ =m _).
      cbn.
      reflexivity.
Abort.


Lemma vec_map_vecn {B C}(f : nat -> B -> C) n (v : B ** n) :
vec_map f v = vec_map (fun _ b => f 0 b) v.
Admitted.

Lemma commonVal_Vec_In1 {B} n0 (v0 : B ** n0)n1 n1' (v1 : B ** n1)(v1' : B ** n1')(h : vec_common_val v1 v1' v0)
      b (inb : Vec_In b v0) : Vec_In b v1.
  Admitted.
Lemma commonVal_Vec_In2 {B} n0 (v0 : B ** n0)n1 n1' (v1 : B ** n1)(v1' : B ** n1')(h : vec_common_val v1 v1' v0)
      b (inb : Vec_In b v0) : Vec_In b v1'.
  Admitted.


Lemma commonPos_Vec_In1 {B} n0 (v0 : B ** n0)n1 (v1 v1' : B ** n1)(h : vec_common_pos v0 v1 v1')
      b (inb : Vec_In b v0) : Vec_In b v1.
  apply vec_common_pos_val in h.
  eapply commonVal_Vec_In1; eassumption.
  Qed.
Lemma commonPos_Vec_In2 {B} n0 (v0 : B ** n0)n1 (v1 v1' : B ** n1)(h : vec_common_pos v0 v1 v1')
      b (inb : Vec_In b v0) : Vec_In b v1'.
  apply vec_common_pos_val in h.
  eapply commonVal_Vec_In2; eassumption.
  Qed.

Lemma commonPos_Vec_inverse  n0 (v0 : nat ** n0)n1 (v1 v1' : nat ** n1)(h : vec_common_pos v0 v1 v1')
      b (d1 : distinct v1)(d2 : distinct v1')(inb : Vec_In b v0) : v1 ̅ ¹ b = v1' ̅ ¹ b.
  rewrite <-  Vec_In_in in inb.
  induction h.
  reflexivity.
  - cbn.
    destruct (b =m b0).
    reflexivity.
    cbn in inb.
    apply Bool.orb_prop in inb.
    destruct inb as [eqb|inb].
    + destruct (b =m b0).
      contradiction.
      cbn in eqb.
      discriminate.
    + 
      cbn in d1,d2.
      apply andb_prop in d1, d2.
      destruct d1 as [d1 d1'].
      destruct d2 as [d2 d2'].

    specialize (IHh d1' d2' inb).
      apply Vec_In_in in inb.
    rewrite !(inverse_vec_value 1).
    f_equal.
    tauto.
    eapply commonPos_Vec_In2; eassumption.
    eapply commonPos_Vec_In1; eassumption.
  - cbn.
      cbn in d1,d2.
      apply andb_prop in d1, d2.
      destruct d1 as [d1 d1'].
      destruct d2 as [d2 d2'].
    specialize (IHh d1' d2' inb).
    (* assert (inb' := inb). *)
    apply Vec_In_in in inb.
    rewrite !(inverse_vec_value 1); revgoals.
    eapply commonPos_Vec_In1; eassumption.
    eapply commonPos_Vec_In2; eassumption.
    cbn.
    destruct (b =m b0);
    destruct (b =m b'); try congruence; subst; exfalso.
    + eapply commonPos_Vec_In1 in inb; [|eassumption].
      eapply Vec_In_in in inb.
      rewrite inb in d1.
      discriminate d1.
    + eapply commonPos_Vec_In2 in inb; [|eassumption].
      eapply Vec_In_in in inb.
      rewrite inb in d2.
      discriminate d2.
    (* I need the distinct hypothesis *)
      Qed.

(*
         (derivₙₛ (Var (S + (V +{ n0}) \ Some o)%s) Z_ren a
            (vec_to_ren
               (vec_map
                  (fun _ : nat =>
                   msubst'
                     (fun o' : option (Om V) =>
                      match deceq_option o' (Some o) with
                      | left _ =>
                          ass_instantiate1
                            (Op
                               (SMVar (exist (fun v : option (Om V) => negb (deceq_option v (Some o))) None eq_refl))
                               (vec_map
                                  (fun a0 b : nat =>
                                   derivₙₛ (Var (S + (V +{ n0}) \ Some o)%s) Z_ren a0
                                     (fun k : nat => Var (S + (V +{ n0}) \ Some o)%s ((v1) ̅ ¹ k)) b) v0))
                      | right b =>
                          ass_instantiate2
                            (Op
                               (SMVar (exist (fun v : option (Om V) => negb (deceq_option v (Some o))) None eq_refl))
                               (vec_map
                                  (fun a b0 : nat =>
                                   derivₙₛ (Var (S + (V +{ n0}) \ Some o)%s) Z_ren a
                                     (fun k : nat => Var (S + (V +{ n0}) \ Some o)%s ((v1) ̅ ¹ k)) b0) v0)) b
                      end)) (vec_range0 (Z_model_data (S + V +{ n0})%s) (arm o)))) n)

*)

Tactic Notation "apply_both" tactic(tac) :=
      etransitivity; [|symmetry; etransitivity] ; [tac | tac | ].


Lemma unifier_spec_factors {V } (t u : T S V) c0 (W := cW c0)(ass := cass c0) c (ind : @unifier_spec _ t u c0 c)
  : exists a , cass c = ass ∘a a 
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
  with unifier_spec_vec_factors {V } (l : list nat)(v1 v2 : vec (T S V) l)
       c0 (W := cW c0)(ass := cass c0) 
       c (ind : @unifier_spec_vec _ _ v1 v2 c0 c):
    exists a , cass c = ass ∘a a .
{
  subst ass.
  destruct ind; cbn; try ((eexists;etransitivity;[|symmetry;apply assignation_comp_idl ];reflexivity)
                         || (eexists; symmetry; apply assignation_comp_idr)).
  - cbn in unifier_spec_vec_factors.
    eapply unifier_spec_vec_factors.
    eassumption.
  - eexists.
    reflexivity.
  - eapply unifier_spec_factors.
    eassumption.
}
{
  subst ass.
  destruct ind; cbn.
  - eexists; symmetry; apply assignation_comp_idr.
  - eapply unifier_spec_factors in H.
    eapply unifier_spec_vec_factors in ind.
    destruct H.
    destruct ind.
    rewrite H.
    rewrite H0.
    rewrite <- assignation_comp_assoc.
    eexists.
    reflexivity.
}
Qed.

Lemma unifier_spec_preserve {V } (t u : T S V) c0 (W := cW c0)(ass := cass c0) c (ind : @unifier_spec _ t u c0 c)
  :
  forall t' u',
  t' [ ass ]ₘ = u' [ ass ]ₘ ->
  t' [  cass c ]ₘ = 
  u' [  cass c ]ₘ.
Proof.
  apply unifier_spec_factors in ind.
  destruct ind as [? eq].
  intros.
  rewrite eq.
  rewrite <- 2!assignation_comp_msubst'.
  f_equal.
  assumption.
Qed.
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
(*
  Lemma unifier_spec_vec_preserve {V } (l : list nat)(v1 v2 : vec (T S V) l)
       c0 (W := cW c0)(ass := cass c0) 
       c (ind : @unifier_spec_vec _ _ v1 v2 c0 c):
  forall t' u',
  t' [ ass ]ₘ = u' [ ass ]ₘ ->
  t' [  cass c ]ₘ = 
  u' [  cass c ]ₘ.
    Proof.
  apply unifier_spec_vec_factors in ind.
  destruct ind as [? eq].
  intros.
  rewrite eq.
  rewrite <- 2!assignation_comp_msubst'.
  f_equal.
  assumption.
  Qed.
*)
  (*
Proof.
{
  subst ass.
  destruct ind; cbn; intros t' u'; rewrite ?msubst'_id; try congruence.
  - cbn.
    intro h.
    eapply unifier_spec_vec_preserve; eassumption.
  - rewrite <- !assignation_comp_msubst'.
    cbn.
    congruence.
  - eapply unifier_spec_preserve.
    eassumption.
}
{
  subst ass.
  destruct ind; cbn; intros t' u'; rewrite ?msubst'_id.
  - congruence.
  - cbn.
    intro h.
    eapply unifier_spec_preserve.
    eassumption.
    eapply unifier_spec_vec_preserve.
    eassumption.
    eassumption.
}
Qed.
*)


(*
Fixpoint factors {A B B' : Type}(f : A -> B)(g : A -> B')
  (hfg : forall t u,
  f t = f u ->
  g t = g u) C (lC : list C) (v1 : vec _ lC) {struct v1 }: forall (v2 : vec _ lC),
    vec_map ( fun _ => f) v1 = vec_map ( fun _ => f) v2
    -> vec_map ( fun _ => g) v1 = vec_map (fun _ => g) v2.
  Admitted.
*)

Lemma unifier_spec_preserve_vec {V } (t u : T S V) c0 (W := cW c0)(ass := cass c0) c (ind : @unifier_spec _ t u c0 c)
  
   (l' : list nat) v1'  : forall v2' : vec (T S V) l', 
     vec_map (fun _ t =>  t [  ass ]ₘ)  v1' =
     vec_map (fun _ t => t [  ass ]ₘ)  v2'  -> 
     vec_map (fun _ t =>  t [  cass c ]ₘ)  v1' =
     vec_map (fun _ t => t [  cass c ]ₘ)  v2'.

  apply unifier_spec_factors in ind.
  destruct ind as [a eq].
  intro v2'.
  intro h.
  assert (H : forall (v : vec (T S V) l'),   vec_map (fun (_ : nat) (t0 : T S V) => t0 [cass c ]ₘ) v =
                                                vec_map (fun (_ : nat) t0 => t0 [ a ]ₘ)
                                                (vec_map (fun (_ : nat) t0 => t0 [ cass c0 ]ₘ)
                                                         v)
            ).
  {
    intro v.
    rewrite vec_map_map.
    apply vec_map_ext.
    intros.
    rewrite eq.
    symmetry.
    apply assignation_comp_msubst'.
  }
  rewrite 2!H.
  f_equal.
  apply h.
  Qed.
  (*
  assumption 
  subst ass.
  apply factors.
  eapply unifier_spec_preserve.
  eassumption.
*)

Lemma unifier_spec_correct {V } (t u : T S V) c0 (W := cW c0)(ass := cass c0) c (ind : @unifier_spec _ t u c0 c) :
  t [  cass c ]ₘ = 
  u [  cass c ]ₘ
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
  with unifier_spec_vec_correct {V } (l : list nat)(v1 v2 : vec (T S V) l)
       c0 (W := cW c0)(ass := cass c0) 
       c (ind : @unifier_spec_vec _ _ v1 v2 c0 c) :
     vec_map (fun _ t =>  t [  cass c ]ₘ)  v1 =
     vec_map (fun _ t => t [  cass c ]ₘ)  v2.
{
  destruct ind.
  - reflexivity.
  - hnf.
    cbn.
    f_equal.
    apply unifier_spec_vec_correct in H.
    apply H.
    (*
  - destruct H.
    reflexivity.
  - (* candidate replace: same mvar *)
    rename X into commonPos.
    cbn -[TMVar_replaced].
    rewrite 2!assignation_replace_TMVar_replaced.
    rewrite !vec_map_vecn.
    cbn.
    f_equal.
    apply_both (apply (f_equal ( fun v => vec_map _ (l := _)(vec_map _ (l := _) v))); apply  replaced_vec_vec_map).
    (*
    etransitivity;[|symmetry; etransitivity];
      try (apply (f_equal ( fun v => vec_map _ (l := _)(vec_map _ (l := _) v))); apply  replaced_vec_vec_map).
*)
    rewrite !vec_map_map.
    cbn.
    unfold replaced_vec.
    destruct (o =m o); [|contradiction].
    apply_both (apply vec_map_vecn).
    (* etransitivity; [|symmetry;etransitivity]; try apply vec_map_vecn. *)
    cbn.

    (* etransitivity;[|symmetry;etransitivity]; *)
      apply_both (
    apply vec_map_ext;
    intros;
    unfold vec_to_ren;
    cbn;
    eapply (vec_nth_map'' _ (  (fun _ b0 : nat => Var (S + V [o := n0])%s b0)) _ 0 )).
    cbn.
    assert(h0 :
            vec_map (fun _ b : nat =>  (vec_nth ((v1) ̅ ¹ b) v2 ((v1) ̅ ¹ b))) v0 =
  vec_map (fun _ b : nat =>  (vec_nth ((v1) ̅ ¹ b) v1 ((v1) ̅ ¹ b))) v0

          ).
    {
      apply vec_map_ext_In.
      intros b inb.
      etransitivity; revgoals.
      - symmetry.
        apply inverse_vec_is_inverse.
        eapply commonPos_Vec_In1; eassumption.
      - erewrite (commonPos_Vec_inverse commonPos ); try assumption.
        apply inverse_vec_is_inverse.
        eapply commonPos_Vec_In2; eassumption.
    }
    eapply (f_equal (vec_map (fun _ => Var _) (l := _))) in h0.
    rewrite 2!vec_map_map in h0.
    exact h0.
*)
      - (* candidate replace bis: same mvar *)
    rename X into commonPos.
    cbn -[TMVar_replaced' assignation_comp].
    cbn.
    unfold assignation_instantiate.
    rewrite (refl_deceq_true (Some o)).
    cbn.
    f_equal.
    rewrite !vec_map_vecn.
    rewrite !vec_map_map.
    cbn.
    rewrite !vec_map_vecn.
    (* apply_both vec_map_vecn. *)
    etransitivity; [|symmetry; etransitivity] ; try apply vec_map_vecn.
    cbn.
    apply vec_map_ext_In.
    intros.
    apply Z_in_fv_subst_ext.
    intros n.
    unfold vec_to_ren.
    cbn.
    unshelve erewrite (vec_nth_map'  _ _ (a := 0) );
      [ eapply Var; shelve | |]; revgoals.
    { cbn.
      reflexivity.
    }
    cbn.
    set (yy := vec_nth _ _  _).
    eassert (hy : yy = _).
    {
      unfold yy.
      apply (vec_to_ren_vec_range0 ( Z_model_data _)).
    }
    rewrite hy.
    cbn.
    intro hn.
    inversion hn.
    apply_both (apply (vec_nth_map' _ _ (a := 0)); reflexivity).
    f_equal.
    assert (inbv1 : Vec_In b v1). { eapply commonPos_Vec_In1; eassumption. }
    assert (inbv2 : Vec_In b v2). { eapply commonPos_Vec_In2; eassumption. }
    rewrite inverse_vec_is_inverse by assumption.
    erewrite commonPos_Vec_inverse by eassumption.
    symmetry.
    apply inverse_vec_is_inverse.
    assumption.

  - (* different mvar *)

    rename X into commonVal.
    cbn -[TMVar_replaced' assignation_comp].
    cbn -[eq_dec].
    unfold assignation_instantiate.
    unshelve erewrite (neq_negb_deceq_false (o' := Some o2)(o := Some o1)).
    congruence.
    unshelve rewrite (refl_deceq_true (Some o1)).
    cbn -[eq_dec].
    assert (neq_o2' : exist (fun v : option (Om V) => negb (deceq_option v (Some o1))) None eq_refl <> o2').
    {
      unfold o2'.
      cbn.
      congruence.
    }
    unshelve erewrite (neq_negb_deceq_false neq_o2').
    cbn -[eq_dec].
    f_equal.
    rewrite !vec_map_vecn.
    rewrite !vec_map_map.
    cbn -[eq_dec].
    rewrite !vec_map_vecn.
    (* apply_both vec_map_vecn. *)
    (* etransitivity; [|symmetry; etransitivity] ; try apply vec_map_vecn. *)
    cbn -[eq_dec].
    assert (eq_o2' :    exist (fun v : option (Om V) => v <>m Some o1) (Some o2)
      (neq_negb_deceq
         (fun H : Some o2 = Some o1 =>
          False_ind False
            (neq_o12 (f_equal (fun t : option (Om V) => match t with
                                                        | Some H0 => H0
                                                        | None => o1
                                                        end) (eq_sym H))))) = o2').
    {
      unfold o2'.
      cbn.
      f_equal.
      apply irrelevance_bool.
    }
    rewrite (deceq_eq_true eq_o2').
    cbn -[eq_dec].
    (*
    assert (h0 : (
       (exist (fun v : {v : option (Om V) | v <>m Some o1} => v <>m o2')
          (exist (fun v : option (Om V) => negb (deceq_option v (Some o1))) None eq_refl) 
          (neq_negb_deceq neq_o2'))

                 )
                   =
                     (exist (fun v : {v : option (Om V) | negb (deceq_option v (Some o1))} => negb (subdeceq v o2'))
          (exist (fun v : option (Om V) => negb (deceq_option v (Some o1))) None eq_refl) eq_refl)
           ).
    {
    cbn.
    f_equal.
    Set Printing Implicit.
    Check (neq_negb_deceq neq_o2').
    }
*)
    set (e' := neq_negb_deceq neq_o2').
    assert (eq_e' : e' = eq_refl (x := true)).
    {
      apply irrelevance_bool.
    }
    change (SMVar (S := S) (V := V +{ n0} \ _ \ _)
       (exist (fun v : {v : option (Om V) | v <>m Some o1} => v <>m o2')
          (exist (fun v : option (Om V) => negb (deceq_option v (Some o1))) None eq_refl) 
          (neq_negb_deceq neq_o2')))
           with (SMVar (S := S) (V := V +{ n0} \ _ \ _)
       (exist (fun v : {v : option (Om V) | v <>m Some o1} => v <>m o2')
          (exist (fun v : option (Om V) => negb (deceq_option v (Some o1))) None eq_refl) 
          e')).
    clearbody e'.
    subst e'.
    cbn -[eq_dec].
    f_equal.
    rewrite !vec_map_map.
    cbn.
    clear eq_o2'.
    etransitivity; revgoals.
    {
      symmetry.
    apply vec_map_vecn.
    }
    cbn.
    apply vec_map_ext_In.
    intros b bv0.
    cbn.
    unfold vec_to_ren.
    etransitivity.
    {
      unshelve erewrite (vec_nth_map'  _ _ (a := 0) ); [ eapply Var; shelve | | cbn; reflexivity].
      set (yy := vec_nth _ _  _).
      eassert (hy : yy = _).
      {
        unfold yy.
        apply (vec_to_ren_vec_range0 ( Z_model_data _)).
      }
      rewrite hy.
      clear yy hy.
      cbn.
      set (yy := vec_nth _ _  _).
      eassert (hy : yy = _).
      {
        unfold yy.
        apply (vec_to_ren_vec_range0 ( Z_model_data _)).
      }
      rewrite hy.
      clear yy hy.
      cbn.
      erewrite (vec_nth_map' _ _ (a := 0)); [ | reflexivity].
      apply (f_equal (Var _)).
      apply inverse_vec_is_inverse.
      eapply commonVal_Vec_In1; eassumption.
    }
    etransitivity; revgoals.
    {
      symmetry.
      set (vmap := vec_map (B := T S (V +{ n0 })) _ _ ).
      eassert (eq_vmap : vmap = _).
      {
         apply vec_map_vecn.
      }
      clearbody vmap.
      subst vmap.
      cbn.
      eassert (vecren := vec_to_ren_vec_range0( Z_model_data (S + (V +{ n0}) \ Some o1)%s) ((v2) ̅ ¹ b)).
      unfold vec_to_ren in vecren.
      cbn in vecren.
      unshelve erewrite (vec_nth_map'  _ _ (a := 0) ); [eapply Var; exact (((v2) ̅ ¹ b)) |  |];revgoals.
      {
        cbn.
        (* eassert (vecren := vec_to_ren_vec_range0( Z_model_data (S + (V +{ n0}) \ Some o1)%s) ((v2) ̅ ¹ b)). *)
        rewrite vecren.
        cbn.
        reflexivity.
      }
      cbn.
      set (yy := vec_nth _ _  _).
      eassert (hy : yy = _).
      {
        unfold yy.
        apply (vec_to_ren_vec_range0( Z_model_data (S + (V +{ n0}) )%s) ((v2) ̅ ¹ b)).
      }
      rewrite hy.
      clear yy hy.
      cbn.
      set (yy := vec_nth _ _  _).
      eassert (hy : yy = _).
      {
        unfold yy.
        apply (vec_to_ren_vec_range0( Z_model_data (S + (V +{ n0}) \Some o1)%s) ((v2) ̅ ¹ b)).
      }
      rewrite hy.
      clear yy hy.
      cbn.
      unshelve eapply (vec_nth_map' _ _ (a := 0)).
      shelve.
      reflexivity.
    }
    f_equal.
    symmetry.
    apply inverse_vec_is_inverse.
    eapply commonVal_Vec_In2; eassumption.
  - apply unifier_spec_correct in ind.
    cbn.
    cbn in ind.
    rewrite <- 2! assignation_comp_msubst'.
    exact ind.
  - (* instantiate *)
    hnf.
    cbn -[remove_mvar].
    unfold assignation_instantiate at 1.
    rewrite (refl_deceq_true o).
    unfold ass_instantiate1.
    cbn.
    cbn in v.
    etransitivity; revgoals.
    {
      symmetry.
      unshelve apply Notin_mvar_msubst.
      assumption.
    }
    etransitivity; [|apply Z_subst_id].
    rewrite Z_subst_subst.
    cbn.
    apply Z_in_fv_subst_ext.
    intros p.
    (* rewrite next_fv_remove_mvar. *)
    intro hp.
    rewrite vec_map_map.
    (* rewrite vec_map_map. *)
    cbn.
    unfold vec_to_ren.
    erewrite (vec_nth_map' _ _ (a := 0)).

    f_equal.
    apply inverse_vec_is_inverse.
    apply hufv.
    eapply In_fv_remove_mvar1.
    eassumption.
    cbn.
    reflexivity.
  - symmetry.
    eapply  unifier_spec_correct.
    eassumption.
    }
{
  destruct ind.
  reflexivity.
  cbn.
  f_equal.
  - specialize (unifier_spec_correct _ _ _ _ _ H).
    (* rewrite assignation_comp_assoc. *)
    apply unifier_spec_correct.
  -
    (* generalize (unifier_spec_vec_correct _ _ _ _ _ _ ind). *)
    eapply unifier_spec_preserve_vec.
    eassumption.
    apply (unifier_spec_vec_correct _ _ _ _ _ _ ind).
}
Qed.



Lemma in_fv_vec_in {S'}(n : nat){p : nat}(v : nat ** p) :
  In_fv_vec n (vec_map (fun _ => Var S') v) ->
  Vec_In n v.
Admitted.

Lemma In_fv_msubst' {V : msignature} {W : msignature}(m := Z_model_data (S + W)%s)
      (f : assignation V m)(t : T S V)(p : nat) : In_fv p t <-> In_fv p (t [ f ]ₘ).
Admitted.

(* not sure how to prove this.
 Use the depth of the expression ? *)
Lemma unified_notin_mvar {V } (t : T S V) {W}  (a : assignation V (Z_model_data (S + W)%s))
         (o : Om V) v
         (* (ht : forall v', vec_map (fun _ => msubst' a) v' = v -> t <> Op (S := S + V)%s (SMVar o) v')  *)
         (ht : forall v',  t <> Op (S := S + V)%s (SMVar o) v') 
      (ha : t [ a ]ₘ = a o v)  :  Notin_mvar o t.
Admitted.

Fixpoint build_vec_common_pos {B : Type}{eqb : EqDec B} (n1 : nat) (v1 : B ** n1) (v1' : B ** n1) : { n0 & B ** n0}.
  Admitted.

Lemma build_vec_common_pos_is_common_pos {B}{eqb : EqDec B}(n1 : nat) (v1 : B ** n1) (v1' : B ** n1)
      : vec_common_pos (projT2 (build_vec_common_pos v1 v1')) v1 v1'.
Admitted.

Fixpoint build_vec_common_val {B : Type}{eqb : EqDec B} (n1 n1' : nat) (v1 : B ** n1) (v1' : B ** n1') : { n0 & B ** n0}.
  Admitted.

Lemma build_vec_common_val_is_common_val {B}{eqb : EqDec B}(n1 n1' : nat) (v1 : B ** n1) (v1' : B ** n1')
      : vec_common_val v1 v1' (projT2 (build_vec_common_val v1 v1')).
Admitted.

(*
This allows double recursion in the same time.
TODO: maybe I can implement directly the algorithm as a fixpoint over
this inductive type
 *)
Inductive valid_pair {V} : T S V -> T S V -> candidate V -> Type :=
  vp_subst : forall c t u, valid_pair (t [ cass c]ₘ)(u [ cass c]ₘ) id_candidate
                      -> valid_pair t u c
  | vp_var_var : forall n n', valid_pair (Var _ n)(Var _ n') id_candidate
  | vp_var_op : forall n o v, valid_pair (Var _ n)(Op (S := S + V)%s(SOp o) v) id_candidate
  | vp_mvar_var : forall n o v, distinct v -> valid_pair (Op (S := S + V)%s(SMVar o) (vec_map (fun _ => Var _) v))(Var _ n) id_candidate
  | vp_mvar_op : forall o v o' v', distinct v' -> valid_pair 
                                          (Op (S := S + V)%s(SMVar o') (vec_map (fun _ => Var _) v'))
                                          (Op (S := S + V)%s(SOp o) v)
                                          id_candidate
| vp_mvar_mvar : forall o v o' v',
    distinct v -> distinct v' ->
    valid_pair (Op (S := S + V)%s(SMVar o) (vec_map (fun _ => Var _) v))
                                          (Op (S := S + V)%s(SMVar o') (vec_map (fun _ => Var _) v'))
                                          id_candidate
| vp_op_op : forall o o' (v : vec (T S V) (ar o))(v' : vec (T S V) (ar o')),
    o <> o' ->
    valid_pair (Op (S := S + V)%s (SOp o) v)
               (Op (S := S + V)%s (SOp o') v')
               id_candidate
| vp_same_op : forall o (v v' : vec (T S V) (ar o)),
    valid_pair_vec v v' id_candidate ->
    valid_pair (Op (S := S + V)%s (SOp o) v)
               (Op (S := S + V)%s (SOp o) v')
               id_candidate

  | vp_sym : forall c t u, valid_pair t u c -> valid_pair u t c
with valid_pair_vec {V}  : forall (l : list nat), vec (T S V) l -> vec (T S V) l -> candidate V -> Type :=
  | vp_nil_nil : forall c, valid_pair_vec NilV NilV c
  (* | vp_cons_nil : forall l (v : vec (T S V) l) a b, valid_pair_vec (ConsV a b v) NilV *)
  (* | vp_nil_cons : forall l (v : vec (T S V) l) a b, valid_pair_vec NilV (ConsV a b v). *)
| vp_cons_cons : forall l (v : vec (T S V) l)(v' : vec (T S V) l) a b b' c0,
                   (forall c, valid_pair b b' c) -> valid_pair_vec v v' c0 ->
    valid_pair_vec (ConsV a b v) (ConsV a b' v') c0.
(*
Inductive valid_pair {V} : T S V -> T S V -> candidate V -> Type :=
    vp_var_var : forall n n', valid_pair (Var _ n)(Var _ n')
  | vp_var_op : forall n o v, valid_pair (Var _ n)(Op (S := S + V)%s(SOp o) v)
  | vp_mvar_var : forall n o v, distinct v -> valid_pair (Op (S := S + V)%s(SMVar o) (vec_map (fun _ => Var _) v))(Var _ n)
  | vp_mvar_op : forall o v o' v', distinct v' -> valid_pair 
                                          (Op (S := S + V)%s(SMVar o') (vec_map (fun _ => Var _) v'))
                                          (Op (S := S + V)%s(SOp o) v)
| vp_mvar_mvar : forall o v o' v',
    distinct v -> distinct v' ->
    valid_pair (Op (S := S + V)%s(SMVar o) (vec_map (fun _ => Var _) v))
                                          (Op (S := S + V)%s(SMVar o') (vec_map (fun _ => Var _) v'))
| vp_op_op : forall o o' (v : vec (T S V) (ar o))(v' : vec (T S V) (ar o')),
    o <> o' ->
    valid_pair (Op (S := S + V)%s (SOp o) v)
               (Op (S := S + V)%s (SOp o') v')
| vp_same_op : forall o (v v' : vec (T S V) (ar o)),
    valid_pair_vec v v' ->
    valid_pair (Op (S := S + V)%s (SOp o) v)
               (Op (S := S + V)%s (SOp o) v')

  | vp_sym : forall t u, valid_pair t u -> valid_pair u t
with valid_pair_vec {V}  : forall (l : list nat), vec (T S V) l -> vec (T S V) l -> Type :=
  | vp_nil_nil : valid_pair_vec NilV NilV
  (* | vp_cons_nil : forall l (v : vec (T S V) l) a b, valid_pair_vec (ConsV a b v) NilV *)
  (* | vp_nil_cons : forall l (v : vec (T S V) l) a b, valid_pair_vec NilV (ConsV a b v). *)
| vp_cons_cons : forall l (v : vec (T S V) l)(v' : vec (T S V) l) a b b',
                   valid_pair b b' -> valid_pair_vec v v' ->
    valid_pair_vec (ConsV a b v) (ConsV a b' v').
*)

Lemma aux V W (a : assignation _ (Z_model_data (S + W)%s)) :
       forall n1 (v1 : _ ** n1),
  vec_map
    (fun (n0 : nat) (x : Z (S + W)%s) =>
     x [derivₛ (Var (S + W)%s) Z_subst n0 (vec_to_ren (m := Z_model_data _) (vec_map (fun _ b : nat => Var (S + W)%s b) v1)) ]ₛ)
    (vec_map (fun _ : nat => msubst' a) (vec_range0 (Z_model_data (S + V)%s) n1))
    =   vec_map (fun _ : nat => Var (S + W)%s) v1 

.
          etransitivity;[ apply vec_map_vecn|].
          cbn.
          rewrite vec_map_map. 
          cbn.
          etransitivity;[ apply vec_map_mk|].
          cbn.
          apply vec_mk_nth0.
          Qed.


Arguments remove_mvar {V} t ov {h}.
Arguments remove_mvar_vec {V} [l] v ov {h}.
(*
following theorem 7 of mcbride first order unification by structural recursion
 *)
Fixpoint unifier_spec_complete {V } (t u : T S V)
                            (* (c0 := id_candidate) *)
                            c0
                            {W} (a : assignation _ (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
         (ha : t [ cass c0 ∘a a ]ₘ = u [ cass c0 ∘a a ]ₘ)  (valid : valid_pair t u c0) {struct valid} : exists c β δ', @unifier_spec _ t u c0 c
                                                                                                                            (* because of the vec case, we can't seperate existence and factorisation of the given assignation a *)
                                                                                                                            (*
moreover, because of the substitution case (last case of MacBride), we need to prove factorisation of the
output/input  at the same time, so this should be proved beforehand, before unifier_spec_factors
                                                                                                                             *)
    /\  cass c = cass c0 ∘a β /\ a = β ∘a δ' /\ assignation_laws δ'
with unifier_spec_complete_vec {V }{l} (v1 : vec (T S V) l)(v2 : vec (T S V) l)
                               (* (c0 := id_candidate) *)
                               c0
                               {W}  (a : assignation _ (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
         (ha : vec_map (fun _ => msubst'  (cass c0 ∘a a) ) v1 = vec_map (fun _ => msubst' (cass c0 ∘a a)) v2) (valid : valid_pair_vec v1 v2 c0) {struct valid} :
  exists c β δ' , unifier_spec_vec v1 v2 c0 c
    /\  cass c = cass c0 ∘a β /\ a = β ∘a δ' /\ assignation_laws δ'.
  {
    (*
    cbn in ha.
    rewrite (assignation_comp_idl (S := S)(V := V)) in ha.
*)
    (*
  enough (h : forall t' u', valid_pair t' u' -> t' [ a ]ₘ = u' [ a ]ₘ ->  {c : candidate _ & unifier_spec t' u' id_candidate c}).
  {
    eexists.
    apply applyass_spec.
    refine (projT2 (h _ _ _ _ )).
    rewrite 2!assignation_comp_msubst'.
    assumption.
  }
*)
  revert ha.
  destruct valid; cbn.
  - 
    intro.
    eapply unifier_spec_complete in valid0; try eassumption; revgoals.
    {
      cbn.
      rewrite (assignation_comp_idl (S := S)(V := cW c)).
      apply_both (eapply (assignation_comp_msubst' (m := Z_model_data (S + _)%s))).
      congruence.
    }
    destruct valid0 as (c0 & β & δ' & un & fc0 & fa & lδ').
    cbn in fc0.
    rewrite (assignation_comp_idl (S := S)(V := cW c)) in fc0.
    subst β.
    repeat eexists.
    + constructor.
      eassumption.
    + cbn.
      reflexivity.
    + eassumption.
    + eassumption.
  - intro ha.
    injection ha.
    intros ->.
    do 3 eexists.
    repeat split.
    + econstructor.
    + cbn.
      symmetry.
      apply assignation_comp_idl.
    + symmetry.
      apply assignation_comp_idl.
    + assumption.
  - discriminate.
  - intro h.
    rewrite vec_map_map in h.
  (*   assert (hv : forall n1 (w : _ ** n1) w',  *)
  (* vec_map *)
  (*   (fun (n0 : nat) (x : Z (S + W)%s) => *)
  (*    x [derivₛ (Var (S + W)%s) Z_subst n0 (vec_to_ren (vec_map (fun _ b : nat => Var (S + W)%s b) w)) ]ₛ) *)
  (*   (vec_map (fun _ : nat => msubst' a) (vec_range0 (Z_model_data (S + V)%s) n1))  *)
  (*    = w'). *)
  (*                       (* (vec_map (fun _ : nat => Var (S + W)%s) w)). *) *)
  (*                       (* (vec_map (fun _ : nat => Var (S + W)%s) w)). *) *)
  (*   { *)
  (*     intros n1 w. *)
  (*     cbn. *)
  (*     intro v0 *)
      
  (*   } *)
    assert (hv : forall n1 (v1 : _ ** n1),
  vec_map
    (fun (n0 : nat) (x : Z (S + W)%s) =>
     x [derivₛ (Var (S + W)%s) Z_subst n0 (vec_to_ren (m := Z_model_data _) (vec_map (fun _ b : nat => Var (S + W)%s b) v1)) ]ₛ)
    (vec_map (fun _ : nat => msubst' a) (vec_range0 (Z_model_data (S + V)%s) n1))
    =   vec_map (fun _ : nat => Var (S + W)%s) v1 

).
    {
      apply aux.
    }
    eassert (h' :   a o (vec_map (fun _ : nat => Var (S + W)%s) v) = Var (S + W)%s n).
    {
          etransitivity;[|apply h].
          etransitivity;[|symmetry; apply alaws].
          f_equal.
          symmetry.
          apply hv.
    }
    (* unfold assignation_laws in alaws. *)
    (* unfold an_assignation_laws in alaws. *)
    (* unfold binding_condition in alaws. *)
    do 2 eexists.
    (* set (δ := assignation_omit a (o := o)). *)
    refine (ex_intro _ ?[δ'] _).
    repeat split.
    + apply applyass_spec.
      cbn.
      rewrite vec_map_map.
      cbn.
      unshelve eapply instantiation_spec.
      {
        constructor.
      }
      intro p.
      intro hin.
      inversion hin.
      subst.
      (* if x ∈ fv (a v⃗), then x ∈ fv v
Maybe show that x ∈ fv t <=> v [ x := x + 1] ≠ v
       *)
      unshelve eapply in_fv_vec_in; revgoals.
      {
        eapply assignation_fv.
        + apply alaws.
        + unshelve erewrite (_ : a o _ = Var _ n); [|constructor].
          exact h'.
      }
    + cbn.
      reflexivity.
    + (* todo: think over it *)
      cbn.
      instantiate (δ' := assignation_omit a (o := o)).
      apply assignation_ext.
      intros o' v'.
      cbn.
      unfold assignation_raw_comp.
      unfold mk_assignation_raw.
      unfold mk_an_assignation_raw.
      unfold assignation_instantiate.
      destruct (o' =m o).
      * subst o'.
        cbn.
         rewrite vec_to_ren_vec_range0.
         enough (eqv' : v' = vec_map (fun _ x => x [ fun p => vec_to_ren v' (v ̅ ¹ p)  ]ₛ)
                              (vec_map (fun _ : nat => Var (S + W)%s) v) ).
         {
           etransitivity.
           {
             eapply (f_equal (a o)).
             exact eqv'.
           }
           etransitivity.
           {
             symmetry.
             etransitivity; [ apply (alaws o)|].
             rewrite vec_map_vecn.
             cbn.
             reflexivity.
           }
           cbn.
           etransitivity.
           {
             apply (f_equal (fun x => x [ _ ]ₛ)).
             exact h'.
           }
           cbn.
           reflexivity.
        }
        rewrite vec_map_map.
         cbn.
         unfold vec_to_ren.
         cbn.
           symmetry.
           eapply (inverse_vec_is_inverse2 v' _ (fun x => _ (v ̅ ¹ x))).
      * cbn.
        unfold assignation_omit.
        cbn.
        symmetry.
        etransitivity;[apply alaws|].
        eapply( f_equal (a o')).
        cbn.
        rewrite vec_map_map.
        (* similar to the proof of hv *)
        cbn.
        rewrite vec_map_vecn.
        cbn.
        etransitivity;[ apply vec_map_mk|].
        cbn.
        apply vec_mk_nth0.
    + apply assignation_omit_laws.
      assumption.
  - (* same proof as the previous one *)
    rewrite vec_map_map.
    cbn.
    intro h.
    eassert (h' : a o' (vec_map (fun _ : nat => Var (S + W)%s) v') = _).
    {
          etransitivity;[|apply h].
          etransitivity;[|symmetry; apply alaws].
          f_equal.
          symmetry.
          apply aux.
    }
    do 2 eexists.
    refine (ex_intro _ ?[δ'] _).
    repeat eexists.
    + unshelve eapply instantiation_spec.
      {
        eapply unified_notin_mvar.
        discriminate.
        symmetry.
        exact h.
      }
      intros p hin.
      (* apply In_fv_Op in hin. *)
      eapply in_fv_vec_in.
      eapply assignation_fv;[apply alaws|].
      unshelve erewrite (_ : a o' _ = _);[|exact h'|].
      eapply In_fv_msubst' in hin.
      cbn in hin.
      exact hin.
    + cbn.
      symmetry.
      apply assignation_comp_idl.
    + cbn.
      instantiate (δ' := assignation_omit a (o := o')).
      apply assignation_ext.
      intros o2 v2.
      cbn.
      unfold assignation_raw_comp.
      unfold mk_assignation_raw.
      unfold mk_an_assignation_raw.
      unfold assignation_instantiate.
      destruct (o2 =m o').
      * subst o2.
        cbn.
         (* rewrite vec_to_ren_vec_range0. *)
         enough (eqv' : v2 = vec_map (fun _ x => x [ fun p => vec_to_ren v2 (v' ̅ ¹ p)  ]ₛ)
                              (vec_map (fun _ : nat => Var (S + W)%s) v') ).
         {
           etransitivity.
           {
             eapply (f_equal (a o')).
             exact eqv'.
           }
           etransitivity.
           {
             symmetry.
             etransitivity; [ apply (alaws o')|].
             rewrite vec_map_vecn.
             cbn.
             reflexivity.
           }
           cbn.
           etransitivity.
           {
             apply (f_equal (fun x => x [ _ ]ₛ)).
             exact h'.
           }
           cbn.
           rewrite remove_mvar_op.
           cbn.
           f_equal.
           rewrite !vec_map_map.
           cbn in a.
           (* rewrite (assignation_comp_idl (m := Z_model_data (S + V)%s) a). *)
           etransitivity.
           {
             apply vec_map_ext.
             intros.
             set  (a' :=  (id_assignation (m := Z_model_data (S + V)%s)∘a a)).
             assert (eqa'' : a' = a).
             {
               unfold a'.
               apply assignation_comp_idl.
             }
             rewrite eqa''.
             reflexivity.
           }
           etransitivity; revgoals.
           {
             apply vec_map_ext.
             intros.
             symmetry.
             etransitivity.
             {
             eapply (f_equal (fun x => x [ _ ]ₛ)).
             etransitivity.
             {
             eapply (f_equal (fun x => (x [ _ ]ₘ : Z_model_data _) )).
             etransitivity.
             {
               apply Z_subst_ext.
               intro n.
               etransitivity.
               {
               apply derivₙₛ_ext.
               reflexivity.
               intros.
               eapply (vec_to_ren_vec_range0 (Z_model_data _)).
               }
               symmetry.
               cbn.
               eapply (var_derivₙ (var := Var _)).
               reflexivity.
             }
             etransitivity.
             {
               eapply (f_equal (fun x => x [ _ ]ₛ)).
               symmetry.
               apply Z_subst_ext.
               eapply (var_derivₙ (var := Var _)).
               reflexivity.
             }
             rewrite Z_subst_subst.
             cbn.
             reflexivity.
             }
             symmetry.
             apply (msubst'_ren ( m := Z_model_data _)).
             }
             cbn.
             etransitivity; [apply Z_subst_subst|].
             cbn.
             apply Z_subst_ext.
             intros.
             rewrite derivₙₛ_derivₙ.
             rewrite derivₙₛ_derivₙ.
             reflexivity.

           }
           cbn.
           set (ind := Notin_mvar_op _ ).
           rewrite <- (remove_mvar_vec_assignation_incl  ind) at 1.
           rewrite vec_map_map.
           apply vec_map_ext.
           intros.
           f_equal.
           etransitivity.
           apply assignation_comp_msubst'.
           unfold assignation_incl.
           f_equal.
           etransitivity.

           symmetry.
           eapply (assignation_omit_postcomp (m := Z_model_data _)).
           f_equal.
           apply assignation_comp_idl.
         }
        rewrite vec_map_map.
         cbn.
         unfold vec_to_ren.
         cbn.
           symmetry.
           eapply (inverse_vec_is_inverse2 _ _ (fun x => _ (v' ̅ ¹ x))).
      * cbn.
        unfold assignation_omit.
        cbn.
        symmetry.
        etransitivity;[apply alaws|].
        f_equal.
        rewrite vec_map_map.
        (* similar to the proof of hv *)
        cbn.
        rewrite vec_map_vecn.
        cbn.
        etransitivity;[ apply vec_map_mk|].
        cbn.
        apply vec_mk_nth0.
    + apply assignation_omit_laws.
      assumption.
  - destruct (o =m o').
    + (* same mvar *)
      subst o'.
      intro h.
      do 2 eexists.
      refine (ex_intro _ ?[δ'] _).
      repeat eexists.
      * eapply same_mvar; try assumption.
        apply build_vec_common_pos_is_common_pos; assumption.
      * symmetry.
        apply assignation_comp_idl.
      * (* TODO: think over it *)
        assert (d := ?δ').
        cbn in d.
        ICI
        Check ?δ'.
        admit.
      * admit.
    + (* different mvar *)
      intro h.
      repeat eexists.
      * unshelve eapply different_mvar; revgoals.
        apply build_vec_common_val_is_common_val.
        assumption.
      * symmetry.
        apply assignation_comp_idl.
      * admit.
        (* TODO *)
      * admit.
  - cbn.
    intro h.
    injection h.
    contradiction.
  - intro eq.
    assert (eq' : (vec_map (fun _ : nat => msubst' a) v) =  (vec_map (fun _ : nat => msubst' a) v')).
    { admit. }
    eapply unifier_spec_complete_vec in v0;[|eassumption|]; revgoals.
    {
      rewrite (assignation_comp_idl (S := S)(V := V)).
      assumption.
    }
    destruct v0 as (c0 & β & δ' & un & fc0 & fa & δl).
    repeat eexists.
    + econstructor.
      eassumption.
    + symmetry.
      apply assignation_comp_idl.
    + rewrite fc0.
      cbn.
      rewrite (assignation_comp_idl (S := S)(V := V)).
      eassumption.
    + assumption.
  - (* symmetric  *)
    intro h.
    eapply (unifier_spec_complete _ _ _ _ _ a alaws) in valid0; revgoals.
    {
      (* rewrite (assignation_comp_idl (S := S)(V := V)). *)
      congruence.
    }
    destruct valid0 as (c0 & β & δ' & un & fc0 & fa & δl).
    repeat eexists.
    + apply sym_spec.
      eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  }
  {
    (*
        cbn in ha.
    rewrite (assignation_comp_idl (S := S)(V := V)) in ha.
*)

    destruct valid.
    - repeat eexists.
      + constructor.
      + symmetry.
        apply assignation_comp_idr.
      + symmetry.
        apply assignation_comp_idl.
      + assumption.
    - cbn in ha.
      eset (c := id_candidate ).
      assert (eqb : b [cass c0 ∘a a ]ₘ = b' [cass c0 ∘a a ]ₘ).
      {
        admit.
      }
      assert (eqv :vec_map (fun _ : nat => msubst' (cass c0 ∘a a)) v = vec_map (fun _ : nat => msubst' (cass c0 ∘a a)) v').
      {
        admit.
      }

      eapply unifier_spec_complete_vec in valid0;[|apply alaws| exact eqv].
      destruct valid0 as (c1 & β & δ' & un & fc1 & fa & δl).

      (* assert (unc1' := unifier_spec_vec_factors unc1). *)
      (* destruct unc1' as [a' eqa']. *)
      specialize (v0 c1).
      eapply unifier_spec_complete in v0; revgoals.
      {
        rewrite fc1.
        rewrite fa  in eqb.
        rewrite assignation_comp_assoc in eqb.
        exact eqb.
      }
      { assumption. }
      destruct v0 as (c2 & β' & δ'' & un' & fc2 & fa' & δl').
      repeat eexists.
      + econstructor.
        * eassumption.
        (*
        eassert (h : _) ; [| exact h ].
        {
          admit.
          (*
        apply_both (apply vec_map_ext; intros
                    ; rewrite (assignation_comp_idl (S := S)(V := V)) ; reflexivity
                   ).

        cbn.
        symmetry.
        exact eqv.
*)
       }
*)
      (* + eassert ( h := (projT2 (unifier_spec_complete _ _ _ _ _ _ alaws _ (v0 _)))). *)
        *  eassumption.
      + rewrite fc2.
        rewrite fc1.
        rewrite <- assignation_comp_assoc.
        reflexivity.
      + rewrite fa.
        rewrite fa'.
        rewrite assignation_comp_assoc.
        reflexivity.
      + assumption.
  }
    Admitted.
Fixpoint unifier_spec_complete {V } (t u : T S V)
                            (* (c0 := id_candidate) *)
                            c0
                            {W} (a : assignation _ (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
      (ha : t [ cass c0 ∘a a ]ₘ = u [ cass c0 ∘a a ]ₘ)  (valid : valid_pair t u) {struct valid} : { c & @unifier_spec _ t u c0 c}
with unifier_spec_complete_vec {V }{l} (v1 : vec (T S V) l)(v2 : vec (T S V) l)
                               (* (c0 := id_candidate) *)
                               c0
                               {W}  (a : assignation _ (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
      (ha : vec_map (fun _ => msubst'  (cass c0 ∘a a) ) v1 = vec_map (fun _ => msubst' (cass c0 ∘a a)) v2) (valid : valid_pair_vec v1 v2) {struct valid} : { c & unifier_spec_vec v1 v2 c0 c}.
  {
    (*
    cbn in ha.
    rewrite (assignation_comp_idl (S := S)(V := V)) in ha.
*)
    (*
  enough (h : forall t' u', valid_pair t' u' -> t' [ a ]ₘ = u' [ a ]ₘ ->  {c : candidate _ & unifier_spec t' u' id_candidate c}).
  {
    eexists.
    apply applyass_spec.
    refine (projT2 (h _ _ _ _ )).
    rewrite 2!assignation_comp_msubst'.
    assumption.
  }
*)
  revert ha.
  destruct valid; cbn.
  - intro ha.
    injection ha.
    intros ->.
    eexists.
    econstructor.
  - discriminate.
  - intro h.
    eexists.
    apply applyass_spec.
    cbn.
    rewrite vec_map_map.
    cbn.
    unshelve eapply instantiation_spec.
    {
      constructor.
    }
    intro p.
    intro hin.
    inversion hin.
    subst.
    (* if x ∈ fv (a v⃗), then x ∈ fv v
Maybe show that x ∈ fv t <=> v [ x := x + 1] ≠ v
     *)
    unshelve eapply in_fv_vec_in; revgoals.
    {
    eapply assignation_fv.
    + apply alaws.
    + rewrite vec_map_map in h.
      cbn in h.
      cbn.
      unshelve erewrite (_ : a o _ = _);[| apply h | ].
      constructor.
      }
  - (* same proof as the previous one *)
    rewrite vec_map_map.
    cbn.
    intro h.
    eexists.
    unshelve eapply instantiation_spec.
    {
      eapply unified_notin_mvar.
      discriminate.
      symmetry.
      exact h.
    }
    intros p hin.
    (* apply In_fv_Op in hin. *)
    eapply in_fv_vec_in.
    eapply assignation_fv;[apply alaws|].
    unshelve erewrite (_ : a o' _ = _);[| apply h | ].
    eapply In_fv_msubst' in hin.
    cbn in hin.
    exact hin.
  - destruct (o =m o').
    + (* same mvar *)
      subst o'.
      intro h.
      eexists.
      eapply same_mvar; try assumption.
      apply build_vec_common_pos_is_common_pos; assumption.
    + (* different mvar *)
      intro h.
      eexists.
      unshelve eapply different_mvar; revgoals.
      apply build_vec_common_val_is_common_val.
      assumption.
  - cbn.
    intro h.
    injection h.
    contradiction.
  - 
    intro eq.
    assert (eq' : (vec_map (fun _ : nat => msubst' a) v) =  (vec_map (fun _ : nat => msubst' a) v')).
    { admit. }
    enough (h : { c & unifier_spec_vec v v' id_candidate c }).
    {
    eexists.
    econstructor.
    exact (projT2 h).
    }
    eapply unifier_spec_complete_vec; try eassumption.

    rewrite (assignation_comp_idl (S := S)(V := V)).
    assumption.
  - (* symmetric  *)
    intro h.
    eapply (unifier_spec_complete _ _ _ _ a alaws) in valid0; revgoals.
    {
      rewrite (assignation_comp_idl (S := S)(V := V)).
      congruence.
    }
    eexists.
    apply sym_spec.
    apply (projT2 valid0).
  }
  {
        cbn in ha.
    rewrite (assignation_comp_idl (S := S)(V := V)) in ha.

    destruct valid.
    - eexists.
      constructor.
    - cbn in ha.
      assert (eqb : b [a ]ₘ = b' [a ]ₘ).
      {
        admit.
      }
      assert (eqv :vec_map (fun _ : nat => msubst' a) v = vec_map (fun _ : nat => msubst' a) v').
      {
        admit.
      }

      eexists.
      econstructor.
      + refine (projT2 (unifier_spec_complete_vec _ _ _ _ _ _ alaws _ _));[|assumption].
        revert eqv.
        shelve.
        (*
        eassert (h : _) ; [| exact h ].
        {
          admit.
          (*
        apply_both (apply vec_map_ext; intros
                    ; rewrite (assignation_comp_idl (S := S)(V := V)) ; reflexivity
                   ).

        cbn.
        symmetry.
        exact eqv.
*)
       }
*)
      +  eassert ( h := (projT2 (unifier_spec_complete _ _ _ _ _ alaws _ v0))).
         cbn in h.
         eapply applyass_spec.
        eapply unifier_spec_complete.
  }
    Admitted.

Fixpoint unifier_spec_complete {V } (t u : T S V) {W}  (a : assignation V (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
      (ha : t [ a ]ₘ = u [ a ]ₘ) (valid : valid_pair t u) {struct valid} : { c & @unifier_spec _ t u id_candidate c}
  with unifier_spec_complete_vec {V }{l} (v1 : vec (T S V) l)(v2 : vec (T S V) l) {W}  (a : assignation V (Z_model_data (S + W)%s))
         (alaws : assignation_laws a)
      (ha : vec_map (fun _ => msubst' a) v1 = vec_map (fun _ => msubst' a) v2) (valid : valid_pair_vec v1 v2) {struct valid} : { c & unifier_spec_vec v1 v2 id_candidate c}.
  {
  revert ha.
  destruct valid; cbn.
  - intro ha.
    injection ha.
    intros ->.
    eexists.
    econstructor.
  - discriminate.
  - intro h.
    eexists.
    unshelve eapply instantiation_spec.
    {
      constructor.
    }
    intro p.
    intro hin.
    inversion hin.
    subst.
    (* if x ∈ fv (a v⃗), then x ∈ fv v
Maybe show that x ∈ fv t <=> v [ x := x + 1] ≠ v
     *)
    unshelve eapply in_fv_vec_in; revgoals.
    {
    eapply assignation_fv.
    + apply alaws.
    + rewrite vec_map_map in h.
      cbn in h.
      cbn.
      unshelve erewrite (_ : a o _ = _);[| apply h | ].
      constructor.
      }
  - (* same proof as the previous one *)
    rewrite vec_map_map.
    cbn.
    intro h.
    eexists.
    unshelve eapply instantiation_spec.
    {
      eapply unified_notin_mvar.
      discriminate.
      symmetry.
      exact h.
    }
    intros p hin.
    (* apply In_fv_Op in hin. *)
    eapply in_fv_vec_in.
    eapply assignation_fv;[apply alaws|].
    unshelve erewrite (_ : a o' _ = _);[| apply h | ].
    eapply In_fv_msubst' in hin.
    cbn in hin.
    exact hin.
  - destruct (o =m o').
    + (* same mvar *)
      subst o'.
      intro h.
      eexists.
      eapply same_mvar; try assumption.
      apply build_vec_common_pos_is_common_pos; assumption.
    + (* different mvar *)
      intro h.
      eexists.
      unshelve eapply different_mvar; revgoals.
      apply build_vec_common_val_is_common_val.
      assumption.
  - cbn.
    intro h.
    injection h.
    contradiction.
  - 
    intro eq.
    assert (eq' : (vec_map (fun _ : nat => msubst' a) v) =  (vec_map (fun _ : nat => msubst' a) v')).
    { admit. }
    enough (h : { c & unifier_spec_vec v v' id_candidate c }).
    {
    eexists.
    econstructor.
    exact (projT2 h).
    }
    eapply unifier_spec_complete_vec; eassumption.
  - (* symmetric  *)
    intro h.
    eapply (unifier_spec_complete _ _ _ _ a alaws) in valid0; [|congruence].
    eexists.
    apply sym_spec.
    apply (projT2 valid0).
  }
  {
    destruct valid.
    - eexists.
      constructor.
    - cbn in ha.
      assert (eqb : b [a ]ₘ = b' [a ]ₘ).
      {
        admit.
      }
      assert (eqv :vec_map (fun _ : nat => msubst' a) v = vec_map (fun _ : nat => msubst' a) v').
      {
        admit.
      }

      eexists.
      econstructor.
      + refine (projT2 (unifier_spec_complete_vec _ _ _ _ _ _ alaws _ _));[|assumption].
        assumption.
      +  eassert ( h := (projT2 (unifier_spec_complete _ _ _ _ _ alaws _ v0))).
         cbn in h.
         eapply applyass_spec.
        eapply unifier_spec_complete.
  }
    Admitted.

Fixpoint unifier_spec_general {V } (t u : T S V) {W}  (a : assignation V (Z_model_data (S + W)%s))
         (ha : t [ a ]ₘ = u [ a ]ₘ)
         {c}
         (ind : unifier_spec t u id_candidate c)
         {struct ind} : { a' : assignation _ _ | forall o v, a o v = (cass c ∘a a') (o := o) v}.
  (* TODO *)
Admitted.
 
(*
      rewrite <- h.
    ICI
    rewrite h in hin.
    apply 
    rewrite In_fv
    econstructor.
    discriminate.
    contradiction.
    
  destruct t; cbn in ha.
  - destruct u; cbn in ha.
    cbn in ha.
      c (ind : @unifier_spec _ t u c0 c) :
  t [  cass c ]ₘ = 
  u [  cass c ]ₘ
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
*)
(*
  with unifier_spec_vec_complete {V } (l : list nat)(v1 v2 : vec (T S V) l)
       c0 (W := cW c0)(ass := cass c0) 
       c (ind : @unifier_spec_vec _ _ v1 v2 c0 c) :
     vec_map (fun _ t =>  t [  cass c ]ₘ)  v1 =
     vec_map (fun _ t => t [  cass c ]ₘ)  v2.
*)

(* ******************

This version is like the previous one but with useless cases
and without the symmetric case

**************** *)
Inductive unifier_spec  : forall V, T S V -> T S V -> forall (acc : candidate V) , candidate V -> Prop :=
  var_spec : forall V n c, @unifier_spec V (Var _ n) (Var _ n) c c
| sop_spec : forall V o v1 v2 c1 c2,
    @unifier_spec_vec V _ v1 v2 c1 c2
    ->
    @unifier_spec V (Op (S := S + V)%s (SOp o) v1) (Op (S := S + V)%s (SOp o) v2) c1 c2
                                     (* TODO correct *)
                  (* TODO: remove *)
| mvar_spec : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) c,
    v1 = v2 ->
    (* TODO: apply c to o *)
    @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                 c c
                 (* TODO: remove: same_mvar_bis is better since it does not require the definition of candidate_replace  *)
| same_mvar : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) 
                n0 v0, vec_common_pos (n0 := n0) v0 v1 v2 ->
                       distinct v1 -> distinct v2 ->
                       @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                                     id_candidate
                                     (candidate_replace (o := o)
                                                (TMVar_replaced (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ))
| same_mvar_bis : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) 
                n0 v0, vec_common_pos (n0 := n0) v0 v1 v2 ->
                       distinct v1 -> distinct v2 ->
                       @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                                     id_candidate
                                     (candidate_replace' (o := o)
                                                (TMVar_replaced' (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ))
| different_mvar : forall V o1 o2 (neq_o12 : o1 <> o2)(v1 : vec nat (ar (s := S + V)%s(SMVar o1)))
                     (v2 : vec nat (ar (s := S + V)%s(SMVar o2)))
                     n0 v0
                    (o2' := exist _ (Some o2) (neq_negb_deceq (neq_Some neq_o12)) : Om (V +{ n0 } \ Some o1))
               , vec_common_val (n0 := n0) v1 v2 v0 ->
                       (* distinct v1 -> distinct v2 -> *)
                       @unifier_spec V (Op (S := S + V)%s (SMVar o1) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o2) (vec_map (fun _ => Var _)v2))
                                     id_candidate
                                     (
                                       id_candidate_ext n0
                                        ∘c candidate_instantiate (V := V +{ n0 }) (o := Some o1)
                                          (TMVar (V := V +{ n0 } \ Some o1)(o := exist _ None eq_refl)
                                                (vec_map (fun _ p => Var _ (v1 ̅ ¹ p)) v0))
                                        ∘c candidate_instantiate (V := V +{ n0 } \ Some o1)
                                          (o := o2') 
                                          (TMVar (V := V +{ n0 } \ Some o1 \ o2')(o := exist _ (exist _ None eq_refl) eq_refl)
                                          (vec_map (fun _ p => Var _ (v2 ̅ ¹ p)) v0))
                                     )
                                     
                                     (* (candidate_comp (r1 :=  *)
                                     
                                     (* candidate_replace (o := o1) *)
                                     (*            (TMVar_replaced (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ)) *)
                                     (* (candidate_instantiate (o := o2) _) *)
                                     (* ) *)

(*
1. m1[x1,..,xn] = m1[y1,..,yn]
  m1 ↦ m3 whose arity the subset where xi = yi
  m1[x1,..,xn] ↦ m3[]

2. m1[x1,..,xn] = m2[y1,..,ym]
  m1,m2 ↦ m3 whose arity the common intersection {x1,..,xn} ∩ {y1,..,ym}

When metavariables are different, you can reorder those parameters in 2. but not in 1.
 *)



| applyass_spec : forall V t u c cf, @unifier_spec _ (t [ cass c ]ₘ) (u [ cass c ]ₘ) id_candidate cf
                                            -> 
                                              @unifier_spec V t u c (c ∘c cf)
(* M[k1,...,kₙ] = t
then M [u1,...,uₙ] = t [kᵢ ↦ uᵢ]
Let us assume to start with that k1,...,kn = 0,..,n-1
and maybe add an instantiation case that replace M[k1, ..., kn] with N[0,..,m]?
 *)
   (* ce qu il faut faire c'est construire un inverse (en tant que nat -> nat) de v (vecteur d'entiers) *)
   (* et ensuite mk_assignation de t[v^-1] *)
| instantiation_spec : forall V (c0 := id_candidate) o (n := arm o) (v : nat ** n)(* (v : nat ** arm o) *) (u : T S V)
                         (hu : Notin_mvar o u)
  (hufv : forall n, In_fv n u -> Vec_In n v), (* next_fv u <= n *)
                          @unifier_spec V
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _) v))
                                            u
                                            c0
                                            (candidate_instantiate (remove_mvar hu [ fun k =>  Var _ (v ̅ ¹ k) ]ₛ))
                                            (* (mk_assignation (m := ZModel (S + V \ o)) ) *)
                                                           (* missing case: instantiation *)
| instantiation_sym_spec : forall V (c0 := id_candidate) o (n := arm o) (v : nat ** n)(* (v : nat ** arm o) *) (u : T S V)
                         (hu : Notin_mvar o u)
  (hufv : forall n, In_fv n u -> Vec_In n v), (* next_fv u <= n *)
                          @unifier_spec V
                                            u
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _) v))
                                            c0
                                            (candidate_instantiate (remove_mvar hu [ fun k =>  Var _ (v ̅ ¹ k) ]ₛ))

with unifier_spec_vec : forall V (l : list nat), vec (T S V) l -> vec (T S V) l -> forall c : candidate V, candidate V -> Prop :=
  NilV_spec : forall V c, @unifier_spec_vec V _ NilV NilV c c
| ConsV_spec : forall V n l t1 t2 (v1 v2 : vec (T S V) l) c1  c1' c2, 
                                                          (* do we need to take n into account? I think n *)
                                        @unifier_spec_vec V _ v1 v2 c1 c1' ->
                                        @unifier_spec V t1 t2 c1' c2 ->
                                        @unifier_spec_vec V _ (ConsV n t1 v1) (ConsV n t2 v2) c1
                                                         c2.

(* ******************

This version produces 
  T S (cW acc) --> T S .. 
rather than T S V --> T S .. (see discussion belw)

**************** *)
(* the first candidate is the accumulator *)
(* should the result be rather a candidate V (as in McBride) than candidate (cW c)?
 *)
                                                 (* T S V --> T S (cW acc) *)
                                                                     (* T S (cW acc) --> T S .. *)
                                                                     (* in mcbride, candidate V T S V --> T S .. *)
Inductive unifier_spec  : forall V, T S V -> T S V -> forall (acc : candidate V) , candidate (cW acc) -> Prop :=
  var_spec : forall V n c, @unifier_spec V (Var _ n) (Var _ n) c id_candidate 
| sop_spec : forall V o v1 v2 c1 c2,
    @unifier_spec_vec V _ v1 v2 c1 c2
    ->
    @unifier_spec V (Op (S := S + V)%s (SOp o) v1) (Op (S := S + V)%s (SOp o) v2) c1 c2
                                     (* TODO correct *)
| mvar_spec : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) c,
    v1 = v2 ->
    (* TODO: apply c to o *)
    @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                 c id_candidate
(*
1. m1[x1,..,xn] = m1[y1,..,yn]
  m1 ↦ m3 whose arity the subset where xi = yi
  m1[x1,..,xn] ↦ m3[]

2. m1[x1,..,xn] = m2[y1,..,ym]
  m1,m2 ↦ m3 whose arity the common intersection {x1,..,xn} ∩ {y1,..,ym}

When metavariables are different, you can reorder those parameters in 2. but not in 1.
 *)
| applyass_spec : forall V t u c cf, @unifier_spec _ (t [ cass c ]ₘ) (u [ cass c ]ₘ) id_candidate cf
                                            -> 
                                              @unifier_spec V t u c cf
                 (*
(* M[k1,...,kₙ] = t
then M [u1,...,uₙ] = t [kᵢ ↦ uᵢ]
Let us assume to start with that k1,...,kn = 0,..,n-1
and maybe add an instantiation case that replace M[k1, ..., kn] with N[0,..,m]?
 *)
| instantiation_spec : forall c0 o (n := arm o) (v := vec_mk 0 (fun x _ => x) (List.repeat 0 n))(* (v : nat ** arm o) *) (u : T S V)(hu : notin_mvar o u) , next_fv u <= n 
                          -> unifier_spec
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v))
                                            u
                                            (candidate_instantiate (remove_mvar hu))
                                            (* (mk_assignation (m := ZModel (S + V \ o)) ) *)
                                                           (* missing case: instantiation *)
*)
with unifier_spec_vec : forall V (l : list nat), vec (T S V) l -> vec (T S V) l -> forall c : candidate V, candidate (cW c) -> Prop :=
  NilV_spec : forall V c, @unifier_spec_vec V _ NilV NilV c id_candidate
| ConsV_spec : forall V n l t1 t2 (v1 v2 : vec (T S V) l) c1  c1' c2, @unifier_spec_vec V _ v1 v2 c1 c1' ->
                                                          (* do we need to take n into account? I think n *)
                                        @unifier_spec V t1 t2 (candidate_comp c1') c2 ->
                                        @unifier_spec_vec V _ (ConsV n t1 v1) (ConsV n t2 v2) c1
                                                         (candidate_comp (r1 :=  c1') c2).


Lemma unifier_spec_correct {V } (t u : T S V) c0 (W := cW c0)(ass := cass c0) c (ind : @unifier_spec _ t u c0 c) :
  t [ ass ∘c cass c ]ₘ = 
  u [ ass ∘c cass c ]ₘ
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
  with unifier_spec_vec_correct {V } (l : list nat)(v1 v2 : vec (T S V) l)
       c0 (W := cW c0)(ass := cass c0) 
       c (ind : @unifier_spec_vec _ _ v1 v2 c0 c) :
     vec_map (fun _ t =>  t [ ass ∘c cass c ]ₘ)  v1 =
     vec_map (fun _ t => t [ ass ∘c cass c ]ₘ)  v2.
{
  destruct ind.
  - reflexivity.
  - hnf.
    cbn.
    f_equal.
    apply unifier_spec_vec_correct.
    assumption.
  - destruct H.
    reflexivity.
  - apply unifier_spec_correct in ind.
    cbn in ind.
    etransitivity;[| etransitivity;[apply ind|symmetry]];
    (etransitivity; [|symmetry; apply assignation_comp_msubst']); f_equal; f_equal; symmetry;
    apply assignation_comp_idl.
}
    (*
  - hnf.
    cbn -[remove_mvar].
    unfold assignation_instantiate at 1.
    rewrite (refl_deceq_true o).
    unfold ass_instantiate1.
    cbn.
    cbn in v.
    etransitivity; revgoals.
    {
      symmetry.
      unshelve apply notin_mvar_msubst.
      assumption.
    }
    etransitivity; [|apply Z_subst_id].
    apply Z_mixed_subst_ext.
    intros p.
    (* rewrite next_fv_remove_mvar. *)
    intro hp.
    rewrite vec_map_map.
    cbn.
    (* assert (hp' : p < n) by lia. *)
    (* strangely enough, I don't need these assumptions! *)
    unfold v.
    rewrite vec_map_mk.
    rewrite vec_nth_mk.
    rewrite <- plus_n_O.
    destruct (List.nth_error _ _); reflexivity.
    *)
{
  destruct ind.
  reflexivity.
  cbn.
  f_equal.
  - specialize (unifier_spec_correct _ _ _ _ _ H).
    rewrite assignation_comp_assoc.
    apply unifier_spec_correct.
  - specialize (unifier_spec_vec_correct _ _ _ _ _ _ ind).
    apply (f_equal (vec_map (fun _ t => t [ cass c2]ₘ) (l := _))) in unifier_spec_vec_correct.
    rewrite 2 ! vec_map_map in unifier_spec_vec_correct.
    etransitivity;[| etransitivity;[apply unifier_spec_vec_correct|symmetry]];
      apply vec_map_ext; intros; rewrite assignation_comp_assoc, assignation_comp_msubst'; reflexivity.
    }

   Qed.

(* ************************


 spec without accumulator for which I can't prove correctness because the
inductive principle is not strong enough


***************************
 *)

Inductive unifier_spec {V} : T S V -> T S V -> candidate V -> Prop :=
  var_spec : forall n, unifier_spec (Var _ n) (Var _ n) id_candidate 
| sop_spec : forall o v1 v2 c,
    unifier_spec_vec v1 v2 c
    ->
    unifier_spec (Op (S := S + V)%s (SOp o) v1) (Op (S := S + V)%s (SOp o) v2) c
                                     (* TODO correct *)
| mvar_spec : forall o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))),
    v1 = v2 ->
    unifier_spec (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 id_candidate
(* M[k1,...,kₙ] = t
then M [u1,...,uₙ] = t [kᵢ ↦ uᵢ]
Let us assume to start with that k1,...,kn = 0,..,n-1
and maybe add an instantiation case that replace M[k1, ..., kn] with N[0,..,m]?
 *)
| instantiation_spec : forall o (n := arm o) (v := vec_mk 0 (fun x _ => x) (List.repeat 0 n))(* (v : nat ** arm o) *) (u : T S V)(hu : notin_mvar o u) , next_fv u <= n 
                          -> unifier_spec
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v))
                                            u
                                            (candidate_instantiate (remove_mvar hu))
                                            (* (mk_assignation (m := ZModel (S + V \ o)) ) *)
                                                           (* missing case: instantiation *)
with unifier_spec_vec {V} : forall (l : list nat), vec (T S V) l -> vec (T S V) l -> candidate V -> Prop :=
  NilV_spec : unifier_spec_vec NilV NilV id_candidate
| ConsV_spec : forall n l t1 t2 (v1 v2 : vec (T S V) l) c1 c2, unifier_spec_vec v1 v2 c1 ->
                                                          (* do we need to take n into account? I think n *)
                                        unifier_spec (t1 [ cass c1 ]ₘ) (t2 [ cass c1 ]ₘ) c2 ->
                                        unifier_spec_vec (ConsV n t1 v1) (ConsV n t2 v2)
                                                         (candidate_comp c2).
  
(*
Fixpoint next_fv_remove_mvar V r u hu {struct u} : next_fv (@remove_mvar V u r hu) = next_fv u.
  destruct u.
  reflexivity.
  destruct o.
  - cbn.
  Admitted.
*)



Lemma unifier_spec_correct' {V W} (t u : T S V) (ass : assignation V (ZModel (S + W)%s)) c (ind : unifier_spec (t [ ass ]ₘ) (u [ ass ]ₘ) c) :
  t [ ass ∘c cass c ]ₘ = 
  u [ ass ∘c cass c ]ₘ
  (* is_unifier (t [ ass ]ₘ) (u [ ass ]ₘ) (m := ZModel (S + _)%s) (cass c) *)
 with unifier_spec_vec_correct' {V W} (l : list nat)(v1 v2 : vec (T S V) l)(ass : assignation V (ZModel (S + W)%s)) c (ind : unifier_spec_vec (vec_map (fun _ t =>  t [ ass ]ₘ) v1) (vec_map (fun _ t =>  t [ ass ]ₘ) v2) c) :
     vec_map (fun _ t =>  t [ ass ∘c cass c ]ₘ)  v1 =
     vec_map (fun _ t => t [ ass ∘c cass c ]ₘ)  v2.
(* ca ne marchera pas car il faut detruire ind, pas t *)
  Abort.

(* le probleme ici c'est qu'on fait des compositions d'assignation pour les vecteurs et que du coup l'hypothese d'induction n'est pas assez forte *)
Lemma unifier_spec_correct {V} (t u : T S V) c (ind : unifier_spec t u c) :
  is_unifier t u (m := ZModel (S + _)%s) (cass c)

 with unifier_spec_vec_correct {V} (l : list nat)(v1 v2 : vec (T S V) l) c (ind : unifier_spec_vec v1 v2 c) :
     vec_map (fun _ t =>  t [ cass c]ₘ)  v1 = 
     vec_map (fun _ t => t [ cass c]ₘ)  v2. 
{
  destruct ind.
  - reflexivity.
  - hnf.
    cbn.
    f_equal.
    apply unifier_spec_vec_correct.
    assumption.
  - destruct H.
    reflexivity.
  - hnf.
    cbn -[remove_mvar].
    unfold assignation_instantiate at 1.
    rewrite (refl_deceq_true o).
    unfold ass_instantiate1.
    cbn.
    cbn in v.
    etransitivity; revgoals.
    {
      symmetry.
      unshelve apply notin_mvar_msubst.
      assumption.
    }
    etransitivity; [|apply Z_subst_id].
    apply Z_mixed_subst_ext.
    intros p.
    (* rewrite next_fv_remove_mvar. *)
    intro hp.
    rewrite vec_map_map.
    cbn.
    (* assert (hp' : p < n) by lia. *)
    (* strangely enough, I don't need these assumptions! *)
    unfold v.
    rewrite vec_map_mk.
    rewrite vec_nth_mk.
    rewrite <- plus_n_O.
    destruct (List.nth_error _ _); reflexivity.
}
{
  destruct ind.
  reflexivity.
  cbn.
  f_equal.
  - (* I need an accumulator! *)
    specialize (unifier_spec_correct ).
    Abort.
