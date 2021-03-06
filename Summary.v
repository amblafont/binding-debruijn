Require Import quotsyntax.
Require Import Lib.

(**
The command:

Check (x ≡ y) 

succeeds if and only if [x] is convertible to [y]

*)
Notation  "x ≡ y"  := ((eq_refl _ : x = y) = eq_refl _) (at level 70, no associativity).

Fail Check (true ≡ false).
Check (true ≡ true).


(**

First we summarize the formalisation for standard binding signatures (syntaxdb.v),
 and then we address syntax with equations (quotsyntax.v)
 *)

Require Import syntaxdb.

(** A binding signature is a type together with an arity *)
Check (fun (O : Type)(ar : O -> list nat) =>
         {| O := O;
            ar := ar |} : signature
      ).



(** We define [Z S] the initial model with as an inductive datatype, parameterized by
the signature *)
(** The two constructors: variables and operations *)
Check (Var : forall S : signature, nat -> Z S).
Check (Op : forall (S : signature) (o : O S), vec (Z S) (ar (s:=S) o) -> Z S).
(** Here, [vec B l] is the type of lists that have same length as l *)
Print vec.

Print Z.

(** The data for a model of a signature S.. *)
Check ((fun (S : signature)
          (* is a type *)
          (X : Type)
          (* with variables, substitution, and operations  *)
          (variables : nat -> X)
          (substitution : (nat -> X) -> X -> X) 
          (ops : forall o : S.(O), vec X (S.(@ar) o) -> X)
        =>
               {| carrier := X;
                  variables := variables;
                  ops := ops; 
                  substitution := substitution |} 

            : model_data S
      )).

(** We use the square bracket notation for substitution *)

Check (fun S (m : model_data S) (x : m) (f : nat -> m) =>
         x [ f ] ≡ substitution f x
      ).

(** On the syntax, we define substitution by induction (we need
actually to define renaming first because Coq does not accept
readily termination) *)
Print Z_subst.
Check (fun (S : signature) => (Z_model_data S : model_data S)
                            ≡
                            {| carrier := Z S;
                               variables := Var S;
                               ops := Op (S:=S);
                               substitution := Z_subst |}
      ).



(** The binding condition: stability by substitution *)
Check (
    fun S (m : model_data S) (o : O S) =>
      binding_condition (variables m)(substitution (m := m)) (ops o)
    ≡ forall (f : nat -> m)(v : vec m (ar (s:=S) o)),
          ops o v [f] = ops o (vec_map (fun (n : nat) (t : m) => t [f ^(n)]) v)).

(** where [f ^ ( n )] is defined by iterating derivation *)
Check (
    fun S (m : model_data S) (f : nat -> m)(n  : nat) =>
      f^( n ) ≡ Nat.iter n 
              (fun g => fun n =>
                       match n with
                         0 => variables m 0
                       | S q => g q [ fun n => variables m (1 + n)]
                       end
              ) f
  ).

(**
Substitution is uniquely characterised by the binding condition
and compatibility with variables
 *)
Check (ZModel_unique_subst :
         forall (S : signature)
           (* a given substitution operation *)
           (s : (nat -> Z S) -> Z S -> Z S),
           (* that commutes with variables  *)
       (forall (f : nat -> Z S) (n : nat), s f (Var S n) = f n) ->
       (* and operations *)
       (forall o : O S, binding_condition (Var S) s (Op o)) ->
       (* which is compatible with pointwise equality of functions
          (obvious with the axiom of function extensionality)
         *)
       (forall f g : nat -> Z S, (forall n : nat, f n = g n) -> forall x : Z S, s f x = s g x) ->
       forall (f : nat -> Z S) (z : Z S),
         s f z = substitution (m := Z_model_data S) f z
      ).


(** Models need to satisfy some laws *)

Check (fun S (m : model_data S) 
         (** Substitution is compatible with pointwise equality of functions
              (this is obvious with function extensionality, but we don't assume
               it)
          *)
    (substitution_ext : forall f g : nat -> m, (forall n : nat, f n = g n) -> forall x : m, x [f] = x [g])
    (* operations are compatible with the substitution (see below) *)
    (ops_subst : forall (o : O S),
        binding_condition (variables m)(substitution (m := m)) (ops o)) 
    (* monadic laws *)
    (variables_subst : forall (x : nat) (f : nat -> m), variables m x [f] = f x)
    (assoc : forall (f g : nat -> m) (x : m), (x [g]) [f] = x [fun n : nat => g n [f]])
    (id_neutral : forall x : m, x [variables m] = x )
    =>
  {| substitution_ext := substitution_ext ;
    variables_subst := variables_subst ;
    ops_subst := ops_subst ;
    assoc := assoc ;
    id_neutral := id_neutral |}
  : is_model m
      ).


(** The syntax is a model *)
Check (Z_model_laws : forall (S : signature), is_model (Z_model_data S)).


(** Morphisms of models *)
Check (fun  
       (S : signature) (X Y : model_data S) 
       (u : X -> Y)
(** [u] is a morphisms of models between [X] and [Y] if it commutes
with variables, substitution, and operations *)
    (variables_mor : forall n, u (variables X n) = variables Y n )
    (substitution_mor : forall (f : nat -> X) (x : X), u (x [ f ]) =
                                              (u x) [ fun x => u (f x) ])
    (ops_mor : forall (o : O S)(v : vec X (ar o)), u (ops o v) =
                                             ops o (vec_map (fun _ => u) v))
    =>
    {| variables_mor := variables_mor ;
       substitution_mor := substitution_mor ;
       ops_mor := ops_mor |}
    : is_model_mor u ).

(** We define an initial morphism by induction from Z to m *)
Check (@ini_mor ≡
  fix ini_mor (S : signature) (m : model_data S) (x : Z S) {struct x} : m :=
         match x with
         | Var _ n => variables m n
         | Op o v => ops o (vec_map (fun _ : nat => ini_mor S m) v)
  end).

(** It indeed induces a model morphism *)
Check (@ini_mor_is_model_mor : forall S (m : model S),
          is_model_mor (X:=ZModel S) (Y:=m) (ini_mor m)).

(** Moreover it is the only such model morphism (up to pw equality)*)
Check (@initial_morphism_unique :
forall S (m : model_data S) (f : ZModel S -> m),
  is_model_mor (X:=ZModel S) (Y:=m) f ->
  forall x : ZModel S, f x = ini_mor m x).



(**

Now, we tackle the equations (quotsyntax.v)


 *)
Require Import quotsyntax.

(** Axiomatization of quotient types *)
Require Import Quot.

(** Given two signatures S and V (for metavariables), we define half-equations
 (which will be either the left handside or the right handside
of the equation) *)
Check  (fun (S : signature)(V : signature) 
     (** To each model m of S, it assigns a m-term parameterized
      by a vector of metavariables *)
    (lift_ops : forall (m : model S), forall (o : O V), vec m (ar o) -> m)
    (** This assignment ought to be compatible with the equations *)
    (lift_ops_subst :
      forall (m : model S) (o : O V),
        binding_condition (variables m) (substitution (m := m))
                          (@lift_ops m o))
    (** It should also be natural in the model, i.e., commutes
       with model morphisms *)
    (lift_ops_natural :
       forall (m1 m2 : model S) (f : model_mor m1 m2)
         (o : O V)(v : vec m1 (ar o)),
         lift_ops m2 o (vec_map (fun _ => f) v)  = f (lift_ops m1 o v))
    =>
  {|
    lift_ops := lift_ops ;
    lift_ops_subst := lift_ops_subst ;
    lift_ops_natural := lift_ops_natural ;
  |} : half_equation S V).


(** An equational theory consists in two half-equations with the same
S and V
 *)
Check  (fun (S : signature)(V : signature)
    (left_handside : half_equation S V)
    (right_handside : half_equation S V)
        =>
  {| main_signature := S;
     metavariables := V;
     left_handside := left_handside ;
     right_handside := right_handside |}
  : equational_theory).


(** A model for an equational theory is a model for the underlying main
 signature that equalises both half equations. *)
Check  (fun (E : equational_theory)
          (m : model E.(main_signature))
          (model_eq : forall (o : O (metavariables E))
                        (v : vec m (ar (s:=metavariables E) o)),
              left_handside E m o v = right_handside E m o v )
=> {| main_model := m ;
     model_eq := model_eq |}
   : model_equational E ).

(** (Morphisms are the same as before) *)

(** Given an equational theory, we define an equivalence relation [rel_Z]
on the initial model of its main signature, with the the following constructors:
*)

(* The left and right handsides must be equal *)
Check (@eqE 
        : forall (E : equational_theory)
            (o : O (metavariables E))
         (v : vec (ZModel (main_signature E)) (ar (s:=metavariables E) o)),
          rel_Z (E:=E)
                (left_handside E (ZModel (main_signature E)) o v)
                (right_handside E (ZModel (main_signature E)) o v)).
(** we enforce reflexivity, symmetry and transitivity *)
Check (reflE : forall E z, @rel_Z E z z).
Check (symE : forall E a b, @rel_Z E b a -> rel_Z a b).
Check (transE : forall E a b c, rel_Z (E := E) a b -> rel_Z b c -> rel_Z a c).
(** and congruence *)
Check (congrE : forall E (o : O (main_signature E)) (v v' : vec _ (ar o)),
    rel_vec (@rel_Z E)  v v' -> rel_Z (Op o v) (Op o v')).

Print rel_Z.

(** This defines indeed an equivalence relation on [Z (main_signature E)] *)
Check (fun E : equational_theory  =>
         ZEr E ≡
            ({| eqv_data := @rel_Z E;
               (** these are witnesses that it is an equivalence relation *)
               eqv_rfl := @reflE E ;
               eqv_sym := @symE E;
               eqv_trs := @transE E
            |} : Eqv (Z _))).

(** We define [ZE] the syntax quotiented by this equivalence relation *)
Check (fun (E : equational_theory) =>
         ZE E ≡
            Z (main_signature E) // ZEr E).

(** projE is the canonical projection *)
Check (@projE : forall (E : equational_theory), Z (main_signature E) -> ZE E).

(** The model structure on the syntax lifts to the quotiented one, making
 [projE] a model morphism *)
Check (@projE_is_model_mor: forall (E : equational_theory),
          is_model_mor
            (X:=ZModel (main_signature E))
            (Y:=ZEModel E) projE).

(** Moreover, [ZE E] satisfies the equation and thus upgrades into
a model [ZEModel_equational] of the equational theory.
 *)
Check (fun (E : equational_theory) =>
         carrier (ZEModel_equational E) ≡ ZE E
      ).

(** we can define a model mophism from [ZE E] to any model that satisfies the
 equation *)
Check (@ini_morE_model_mor : forall (E : equational_theory)
                               (m : model_equational E), model_mor (ZEModel_equational E) m).

(** It is actually unique *)
Check (@ini_morE_unique : 
         forall (E : equational_theory) (m : model_equational E)
           (f : model_mor (ZEModel_equational E) m)
           (z : ZE E), f z = ini_morE_model_mor m z).


(**

As an example: lambda-calculus modulo β and η.
First we need to define the signature for lambda-calculus without equation

 *)
Check ((LC_sig : signature) ≡
  {| O := LC_O;
     ar := fun o => match o with
                   App => 0 :: 0 :: nil
                 | Abs => 1 :: nil
                 end
  |}).


(**
Then we need to define the signature for the metavariables.
As we enforce two equations, beta and eta, there are two operations.

 *)

Check ((LCβη_metavariables : signature) ≡
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
  |}).

(**
Now, we can define the equational theory for lambda calculus modulo beta and eta is defined
as follows:
 *)
Check (LCβη_sig ≡
  {|
  main_signature := LC_sig;
  metavariables := LCβη_metavariables ;
  left_handside := _ ;
  right_handside := _ ;
  |}).

(**
The left/right handsides are defined as follows, for beta and then for eta.
 *)

Check (fun (m : model LC_sig) (x y : m) =>
         left_handside LCβη_sig m Beta  (x :: y :: NilV)%v ≡ app (abs x) y
      /\ right_handside LCβη_sig m Beta  (x :: y :: NilV)%v ≡
                        x [ fun n => match n with 0 => y | S p => variables m p end ]).

Check (fun (m : model LC_sig) t =>
         left_handside LCβη_sig m Eta (t :: NilV)%v ≡ t
      /\ right_handside LCβη_sig m Eta (t :: NilV)%v ≡
            (abs (app (t [ fun n => variables m (1 + n) ]) (variables m 0)))
      ).

