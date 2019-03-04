(* Lambda calculus workout *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Arith.
Require Import Id.

From hahn Require Import HahnBase.

(* Lambda term in regular named representation *)
Inductive term : Type := 
  Var  : id -> term
| Abs  : id -> term -> term 
| App  : term -> term -> term.

(* Notations and some examples *)
Notation "\ x , .. , z --> t" := (Abs x .. (Abs z t) .. ) (at level 38, no associativity).
Notation "m @ n"              := (App m n) (at level 39, left associativity).

Definition f := Id 0.
Definition g := Id 1.
Definition h := Id 2.

Definition x := Id 3.
Definition y := Id 4.

Definition m := Id 5.
Definition n := Id 6.

Definition v i := Var i.
           
Definition i     := \ x --> v x.
Definition apply := \ f, x --> (v f @ v x).
Definition z     := \ f, x --> v x.
Definition s     := \ n, f, x --> (v f @ (v n @ v f @ v x)).
Definition add   := \ n, m, f, x --> (v m @ v f @ (v n @ v f @ v x)).
Definition mul   := \ n, m, f, x --> (v m @ (v n @ v f) @ v x).

(* Height of terms *)
Fixpoint height (t : term) : nat :=
  match t with
  | Var _     => 0
  | \ _ --> m => 1 + height m
  | m @ n     => 1 + max (height m) (height n)
  end.

(* Free variables*) 
Inductive fv : id -> term -> Prop :=
  fv_Var : forall x,  fv x (v x)
| fv_Abs : forall x y t,  fv y t -> x <> y -> fv y (\ x --> t)
| fv_App : forall x a b,  (fv x a) \/ (fv x b) -> fv x (a @ b).

Lemma fv_var: forall x y, fv x (v y) -> x = y.
Proof. admit. Admitted.

(* Capture-avoiding substitution *)
Reserved Notation "m [[ x <~ y ]] n" (at level 40, left associativity).

Inductive cas : term -> id -> id -> term -> Prop :=
  cas_Var     : forall x y,
    (v x) [[x <~ y]] (v y)

| cas_Var_neq : forall x y z (NEQ : x <> z),
    (v z) [[x <~ y]] (v z)

| cas_App     : forall m n m' n' x y 
                       (CASM : m [[ x <~ y ]] m')
                       (CASN : n [[ x <~ y ]] n'),
    (m @ n) [[ x<~ y ]] (m' @ n')

| cas_Lam     : forall m x y,
    (\x --> m) [[ x <~ y ]] (\x --> m)

| cas_Lam_neq : forall m m' x y z
                       (NEQX : z <> x) (NEQY : z <> y)
                       (CASM : m [[ x<~ y ]] m'),
    (\ z --> m) [[ x <~ y ]] (\z --> m')

| cas_Lam_ren : forall m m' m'' x y z
                       (NFV : ~ fv z m)
                       (CASM  : m [[ y <~ z ]] m')
                       (CASM' : m' [[ x <~ y ]] m''),
    (\y --> m) [[ x <~ y ]] (\z --> m'')

where "m [[ x <~ y ]] n" := (cas m x y n).

Hint Constructors cas.

(* Some lemmas about CAS *)
Lemma cas_reflexive s x : s [[ x <~ x ]] s.
Proof. admit. Admitted.

Lemma cas_preserves x y z s s' (NEQX : z <> x) (NEQY : z <> y)
      (CAS : s [[x <~ y ]] s') (FV : fv z s'):
  fv z s.
Proof. admit. Admitted.

Lemma cas_renames_free s s' x y (NEQ : x <> y)
      (CAS : s [[ x <~ y ]] s') :
  ~ fv x s'.
Proof. admit. Admitted.

(* Renaming of variables *)
Reserved Notation "m [[ x <~ y ]]" (at level 37, left associativity).

Fixpoint rename t x y :=
  match t with
  | Var z     => if id_eq_dec z x then v y else t
  | \ z --> m => if id_eq_dec z x then t else \ z --> m [[x <~ y]]
  | m @ n     => m [[x <~ y]] @ n [[x <~ y]]
  end
where "m [[ x <~ y ]]" := (rename m x y).

(* Safety condition for renaming *)
Inductive safe : term -> id -> id -> Prop :=
  safe_Var   : forall x y z (NEQ : x <> z),
    safe (Var x) y z

| safe_App   : forall m n x y (SAFEM : safe m x y) (SAFEN : safe n x y),
    safe (m @ n) x y

| safe_Lam_1 : forall m z y (NFV : ~ fv y m), safe (\ z --> m) z y
| safe_Lam_2 : forall m x y z (NEQY : y <> z) (NEQX : x <> z)
                      (SAFEM : safe m x y),
    safe (\ z --> m) x y

| safe_Lam_3 : forall m x z (NEQX : x <> z) (NFV : ~ fv x m),
    safe (\ z --> m) x z.

(* Some lemmas about safety and renaming *)
Lemma safe_nfv m x y (SAFEM : safe m x y) : ~ fv y m.
Proof. admit. Admitted.

Lemma safe_fv_neq m x y z (SAFEM : safe m x y) (FV : fv z m) : y <> z.
Proof. admit. Admitted.

Lemma rename_not_fv m x z (NEQ : x <> z) : ~ fv x (m [[x <~ z]]).
Proof. admit. Admitted.

Lemma safe_reverse m x y (SAFEM : safe m x y) :
  safe (m [[x <~ y]]) y x.
Proof. admit. Admitted.

Hint Resolve safe_reverse.

Lemma rename_height m x y : height m = height (m [[ x <~ y ]]).
Proof. admit. Admitted.

Lemma rename_eq_eq m x : m [[ x <~ x]] = m.
Proof. admit. Admitted.
  
Lemma rename_not_free_is_id m x y (FH : ~ fv x m) : m [[ x <~ y ]] = m.
Proof. admit. Admitted.

Lemma rename_reverse m x y (SH : safe m x y) : (m [[x <~ y]]) [[y <~ x]] = m.
Proof. admit. Admitted.

Lemma rename_preserves m x z y (FH : fv x m) (NEH : z <> x) : fv x (m [[ z <~ y ]]).
Proof. admit. Admitted.

Lemma rename_free_reverse x y z m (HXZ: x <> z) (HYZ: x <> y) (HFV: fv x (m [[ z <~ y]])) : fv x m.
Proof. admit. Admitted.

Lemma rename_if_free m x y z (HFV : fv x (m [[ y <~ z ]])) (HXZ : x <> z) : y <> x.
Proof. admit. Admitted.

Hint Resolve rename_reverse.

(* Contexts *)
Inductive Context : Set :=
  CHole : Context
| CAbs  : id -> Context -> Context
| CAppL : Context -> term -> Context
| CAppR : term -> Context -> Context.

(* Substitution in a context *)
Fixpoint term_in_context (C : Context) (t : term) : term :=
  match C with
  | CHole     => t
  | CAbs x c  => Abs x (term_in_context c t)
  | CAppL c p => App (term_in_context c t) p
  | CAppR p c => App p (term_in_context c t)
  end.

(* Some lemmas about contexts *)
Lemma term_in_context_height a b (C : Context) (HH : height a = height b) : height (term_in_context C a) = height (term_in_context C b).
Proof. admit. Admitted.

Lemma fv_in_term_in_context
      (C : Context) (m : term) (x : id) : fv x (term_in_context C m) -> fv x (term_in_context C (\ x --> v x)) \/ fv x m.
Proof. admit. Admitted.

Lemma fv_in_context
      (C : Context) (m : term) (x : id) : fv x (term_in_context C (\ x --> v x)) -> fv x (term_in_context C m).
Proof. admit. Admitted.

Lemma fv_in_another_term_in_context
      (C : Context) (m n : term) (x : id) (FVM : fv x m) (FVC : fv x (term_in_context C m)) : fv x n -> fv x (term_in_context C n).
Proof. admit. Admitted.

Lemma empty_context m n (H : term_in_context CHole m = n) : m = n.
Proof. admit. Admitted.

Lemma term_in_context_is_var m x C (H : term_in_context C m = v x) : C = CHole.
Proof. admit. Admitted.

(* Alpha conversion *)
Inductive alpha_rename : term -> term -> Prop :=
  alphaRename : forall m x y (HS: safe m x y), alpha_rename (\ x --> m) (\ y --> m [[ x <~ y ]]).

Lemma alpha_rename_height m n (HA : alpha_rename m n) : height m = height n.
Proof. admit. Admitted.

Reserved Notation "m <~~> n" (at level 38, no associativity).

(* Alpha equivalence *)
Inductive alpha_equivalent : term -> term -> Prop :=
| ae_Refl    : forall m, m <~~> m
| ae_Rename  : forall m n, alpha_rename m n -> m <~~> n
| ae_Subterm : forall m n C a b, a <~~> b -> term_in_context C a = m -> term_in_context C b = n -> m <~~> n
| ae_Symm    : forall m n, m <~~> n -> n <~~> m
| ae_Trans   : forall m n p, m <~~> n -> n <~~> p -> m <~~> p
where "m <~~> n" := (alpha_equivalent m n).

Hint Constructors alpha_equivalent.

Ltac inv_conj := repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end).

(* Some tests on alpha-equivalence *)
Module SmokeTest.
  
  Lemma test1 (NEQ: x <> y /\ x <> f /\ y <> f) :
    (v y @ (\x --> (v x @ v y))) <~~> (v y @ (\ f --> (v f @ v y))).
  Proof. admit. Admitted.
  
  Lemma test2 (NEQ : x <> y) :
    ((\x --> v x) @ (\ y --> v y)) <~~> ((\y --> v y) @ (\x --> v x)).
  Proof. admit. Admitted.
  
  Lemma test3 (NEQ : x <> y /\ f <> g /\ x <> f /\ x <> g /\ y <> f /\ y <> g) :
    (\ x --> (v x @ (\ y --> (v x @ v y)))) <~~>  (\ f --> (v f @ (\ g --> (v f @ v g)))).
  Proof. admit. Admitted.
  
End SmokeTest.

(* Some lemmas about alpha-equivalence *)
Lemma alpha_height m n (HA : m <~~> n) : height m = height n.
Proof. admit. Admitted.


Hint Resolve rename_preserves.
Hint Resolve safe_fv_neq.
Hint Resolve rename_free_reverse.

Lemma fv_in_alpha_rename (m n : term) (HA : alpha_rename m n) : forall x, fv x m <-> fv x n.
Proof. admit. Admitted.

Hint Resolve fv_in_alpha_rename.
Hint Resolve fv_in_term_in_context.
Hint Resolve fv_in_context.
Hint Resolve fv_in_another_term_in_context.

Lemma fv_in_alpha_equivalent (m n : term) (HA : m <~~> n) : forall x, fv x m <-> fv x n.
Proof. admit. Admitted.


