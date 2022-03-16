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
Require Import Decidable.
From Equations Require Import Equations.

Open Scope program_scope.
Open Scope list_scope.

Require Import Lib.
Require Import syntaxdb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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


(*
Instance deceq_option {A}{_ : EqDec A} : EqDec (option A).
intros a a'.
decide equality.
Qed.
*)

Lemma refl_deceq_true {A}{_ : EqDec A} (a : A) : a =m a = left eq_refl. 
  Admitted.
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

Inductive In_fv {S } (p : nat) : Z S -> Type :=
  fv_var : In_fv p (Var _ p)
| fv_op : forall (o : O S) (v : vec (Z S) (ar o)), In_fv_vec p v ->
                                                  In_fv p (Op o v)
with In_fv_vec {S } (p : nat) : forall (l : list nat), vec (Z S) l -> Type :=
| fv_hdV : forall a b l v, In_fv (p + a) b -> In_fv_vec p (ConsV a (lA := l) b v)
| fv_tlV : forall a b l v, In_fv_vec p v -> In_fv_vec p (ConsV a (lA := l) b v).


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

Fixpoint vec_mk_ext {A B} n (f g : nat -> A -> B)(l : list A) :
  (forall p a, p >= n -> f p a = g p a) -> vec_mk n f l = vec_mk n g l.
  intro hfg.
  refine
  (match l with
    nil => _
  | cons a lA => _
  end).
  reflexivity.
  cbn.
  f_equal.
  apply hfg.
  constructor.
  apply vec_mk_ext.
  intros.
  apply hfg.
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



Definition assignation_raw_comp {S V W1 W2} {m : model_data (S + W2)%s}
  (a1 : assignation_raw V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 m) : assignation_raw V m.
intro o.
set (t := a1 o).
refine (t [ a2 ]ₘ).
Defined.


Definition assignation_comp {S V W1 W2} {m : model_data (S + W2)%s}
  (a1 : assignation V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 m) : assignation V m.
  apply mk_assignation.
  eapply assignation_raw_comp.
  exact (mk_assignation_raw a1).
  exact a2.
Defined.

Infix "∘c" := assignation_comp (at level 30).

Lemma assignation_comp_assoc {S V W1 W2 W3} {m : model_data (S + W3)%s}
  (a1 : assignation V (ZModel (S + W1)%s)) 
  (a2 :assignation W1 (ZModel (S + W2)%s))
  (a3 :assignation W2 m)
  : a1 ∘c (a2 ∘c a3) = (a1 ∘c a2) ∘c a3.
Admitted.

Lemma assignation_comp_idr {S V W} 
  (a1 : assignation V (Z_model_data (S + W)%s)) 
   : a1 ∘c id_assignation (m := _) = a1.
  Admitted.
Lemma assignation_comp_idl {S V W} {m : model_data (S + W)%s}
  (a1 : assignation V m) 
   : id_assignation (m := _) ∘c a1  = a1.
  Admitted.


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


Definition default_ass {V} : candidate V := mk_candidate (id_assignation (m := ZModel (S + V)%s)).

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
  make_unifier (Var _ n) (Var _ m) := mk_opt default_ass ( Nat.eqb n m) ;
  make_unifier (Op (SOp o1) v1) (Op (SOp o2) v2) := _;
  make_unifier _ _ := mk_opt default_ass false.
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
     (Var _ n, Var _ m) => mk_opt default_ass ( Nat.eqb n m)
   | (Op o1 v1, Op o2 v2) => _
   | _ => mk_opt default_ass false
    end).
  - clear t u.
    revert v1 v2.
    refine (match o1 with
              SOp o1' => match o2 with
                          SOp o2' => _
                        | _ => fun _ _ => mk_opt default_ass false
                        end
            | _ => fun _ _ => mk_opt default_ass false
            end
           ).
    refine (if eqO o1' o2' then _ else fun _ _ => mk_opt default_ass false).
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
    exact (retl default_ass).
    Abort. (* termination !! *)

(* think of unifying t [ c ] and u *)
Fixpoint make_unifier {V }(t : T S V) (c : candidate V) (u : T S (cW c)) {struct t }: lazy_opt (candidate V).
  refine 
  (match (t, u) with
     (Var _ n, Var _ m) => mk_opt default_ass ( Nat.eqb n m)
   | (Op o1 v1, Op o2 v2) => _
   | _ => mk_opt default_ass false
    end).
  - clear t u.
    revert v1 v2.
    refine (match o1 with
              SOp o1' => match o2 with
                          SOp o2' => _
                        | _ => fun _ _ => mk_opt default_ass false
                        end
            | _ => fun _ _ => mk_opt default_ass false
            end
           ).
    refine (if eqO o1' o2' then _ else fun _ _ => mk_opt default_ass false).
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
    exact (retl default_ass).
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
              

Definition msignature_without (V : msignature) (o : Om V) : msignature :=
  {| Om := { v | v <>m o}; arm := fun o' => arm (proj1_sig o') |}.

Infix "\" := @msignature_without (at level 30).


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
Definition ass_instantiate1 {V} {o o' : Om V}(a : T S (V \ o)) :
  an_assignation (arm o') (ZModel (S + V \ o)%s).
   apply mk_an_assignation.
   exact a.
Defined.

Definition ass_instantiate2 {V} {o o' : Om V}(a : T S (V \ o)) 
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
  t [ a ∘c a' ]ₘ. 
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
Fixpoint vec_in (A B : Type){eqb : EqDec B} (b : B) (l : list A)(v : vec B l) : bool :=
  match v with
    NilV => false
  | ConsV a b' v => (b =m b') || vec_in b v
    end.


Lemma Vec_In_in 
      (A B : Type){eqb : EqDec B} (b : B) (l : list A)(v : vec B l) : vec_in b v <-> Vec_In b v.
Admitted.

Fixpoint distinct (A B : Type){eqb : EqDec B} (l : list A)(v : vec B l) : bool :=
  match v with
    NilV => true
  | ConsV a b' v => (negb (vec_in b' v)) && distinct v
    end.

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
  cbn.
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

(* thanks to applyass_spec,
   we can always assume that the input is the identity *)
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
| same_mvar : forall V o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))) 
                n0 v0, vec_common_pos (n0 := n0) v0 v1 v2 ->
                       distinct v1 -> distinct v2 ->
                       @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                                     (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v2))
                                     default_ass
                                     (candidate_replace (o := o)
                                                (TMVar_replaced (vec_map (fun _ => Var _)v0)[ fun k =>  Var _ (v1 ̅ ¹ k) ]ₛ))

(*
1. m1[x1,..,xn] = m1[y1,..,yn]
  m1 ↦ m3 whose arity the subset where xi = yi
  m1[x1,..,xn] ↦ m3[]

2. m1[x1,..,xn] = m2[y1,..,ym]
  m1,m2 ↦ m3 whose arity the common intersection {x1,..,xn} ∩ {y1,..,ym}

When metavariables are different, you can reorder those parameters in 2. but not in 1.
 *)



| applyass_spec : forall V t u c cf, @unifier_spec _ (t [ cass c ]ₘ) (u [ cass c ]ₘ) default_ass cf
                                            -> 
                                              @unifier_spec V t u c (candidate_comp (r1 := c) cf)
(* M[k1,...,kₙ] = t
then M [u1,...,uₙ] = t [kᵢ ↦ uᵢ]
Let us assume to start with that k1,...,kn = 0,..,n-1
and maybe add an instantiation case that replace M[k1, ..., kn] with N[0,..,m]?
 *)
   (* ce qu il faut faire c'est construire un inverse (en tant que nat -> nat) de v (vecteur d'entiers) *)
   (* et ensuite mk_assignation de t[v^-1] *)
| instantiation_spec : forall V (c0 := default_ass) o (n := arm o) (v : nat ** n)(* (v : nat ** arm o) *) (u : T S V)
                         (hu : Notin_mvar o u)
  (hufv : forall n, In_fv n u -> Vec_In n v), (* next_fv u <= n *)
                          @unifier_spec V
                                            (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _) v))
                                            u
                                            c0
                                            (candidate_instantiate (remove_mvar hu [ fun k =>  Var _ (v ̅ ¹ k) ]ₛ))
                                            (* (mk_assignation (m := ZModel (S + V \ o)) ) *)
                                                           (* missing case: instantiation *)
(*
M[x1, ..., xn]
introduce new metavar N
M[x1,...,xn] ↦ N[0,.., max(xn)-1] 
*)
                                            (*
| normalise_mvar : forall V c0 o (n := arm o)(v : nat ** n) (u : T S V)
                     (c' := {| cW := {| Om := Om V;
                                       arm := fun o' => if o =m o' then arm o' else arm o'
                                     |} ;
                     cass := normalise_mvar_vec v
                     |}),
    @unifier_spec V (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _) v)) u
                  c0 c'
*)
with unifier_spec_vec : forall V (l : list nat), vec (T S V) l -> vec (T S V) l -> forall c : candidate V, candidate V -> Prop :=
  NilV_spec : forall V c, @unifier_spec_vec V _ NilV NilV c default_ass
| ConsV_spec : forall V n l t1 t2 (v1 v2 : vec (T S V) l) c1  c1' c2, @unifier_spec_vec V _ v1 v2 c1 c1' ->
                                                          (* do we need to take n into account? I think n *)
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

Lemma vec_map_ext_In {A B C} (f g :  B -> C)(l : list A)(v : vec B l)
      (eq_fg : forall (b : B), Vec_In b v -> f b = g b) :
  vec_map (fun _ => f) v =
  vec_map (fun _ => g) v.
  Admitted.

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


Lemma commonPos_Vec_In1 {B} n0 (v0 : B ** n0)n1 (v1 v1' : B ** n1)(h : vec_common_pos v0 v1 v1')
      b (inb : Vec_In b v0) : Vec_In b v1.
  Admitted.
Lemma commonPos_Vec_In2 {B} n0 (v0 : B ** n0)n1 (v1 v1' : B ** n1)(h : vec_common_pos v0 v1 v1')
      b (inb : Vec_In b v0) : Vec_In b v1'.
  Admitted.

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
  - destruct H.
    reflexivity.
  - (* candidate replace: same mvar *)
    rename X into commonPos.
    cbn -[TMVar_replaced].
    rewrite 2!assignation_replace_TMVar_replaced.
    rewrite !vec_map_vecn.
    cbn.
    f_equal.
    etransitivity;[|symmetry; etransitivity];
      try (apply (f_equal ( fun v => vec_map _ (l := _)(vec_map _ (l := _) v))); apply  replaced_vec_vec_map).
    rewrite !vec_map_map.
    cbn.
    unfold replaced_vec.
    destruct (o =m o); [|contradiction].
    etransitivity; [|symmetry;etransitivity]; try apply vec_map_vecn.
    cbn.

    etransitivity;[|symmetry;etransitivity];
      try (
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
  - apply unifier_spec_correct in ind.
    cbn.
    cbn in ind.
    rewrite <- 2! assignation_comp_msubst'.
    exact ind.
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
    erewrite vec_nth_map'.

    f_equal.
    apply inverse_vec_is_inverse.
    apply hufv.
    eapply In_fv_remove_mvar1.
    eassumption.
    shelve.
    cbn.
    reflexivity.
    }
{
  destruct ind.
  reflexivity.
  cbn.
  f_equal.
  - specialize (unifier_spec_correct _ _ _ _ _ H).
    (* rewrite assignation_comp_assoc. *)
    apply unifier_spec_correct.
  - generalize (unifier_spec_vec_correct _ _ _ _ _ _ ind).
    revert H.
    (* There we should prove that if the input c1 unfies, then the output c2 also does*)
    admit.
    Admitted.
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
  var_spec : forall V n c, @unifier_spec V (Var _ n) (Var _ n) c default_ass 
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
                 c default_ass
(*
1. m1[x1,..,xn] = m1[y1,..,yn]
  m1 ↦ m3 whose arity the subset where xi = yi
  m1[x1,..,xn] ↦ m3[]

2. m1[x1,..,xn] = m2[y1,..,ym]
  m1,m2 ↦ m3 whose arity the common intersection {x1,..,xn} ∩ {y1,..,ym}

When metavariables are different, you can reorder those parameters in 2. but not in 1.
 *)
| applyass_spec : forall V t u c cf, @unifier_spec _ (t [ cass c ]ₘ) (u [ cass c ]ₘ) default_ass cf
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
  NilV_spec : forall V c, @unifier_spec_vec V _ NilV NilV c default_ass
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
  var_spec : forall n, unifier_spec (Var _ n) (Var _ n) default_ass 
| sop_spec : forall o v1 v2 c,
    unifier_spec_vec v1 v2 c
    ->
    unifier_spec (Op (S := S + V)%s (SOp o) v1) (Op (S := S + V)%s (SOp o) v2) c
                                     (* TODO correct *)
| mvar_spec : forall o (v1 v2 : vec nat (ar (s := S + V)%s(SMVar o))),
    v1 = v2 ->
    unifier_spec (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 (Op (S := S + V)%s (SMVar o) (vec_map (fun _ => Var _)v1))
                 default_ass
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
  NilV_spec : unifier_spec_vec NilV NilV default_ass
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
