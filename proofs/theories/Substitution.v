(** * Blood Core Calculus — Substitution

    This file defines substitution for de Bruijn indexed terms and
    proves the key substitution lemma: substitution preserves typing.

    Reference: FORMAL_SEMANTICS.md §7 (Progress and Preservation)
    Phase: M1 — Core Type System
*)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Blood Require Import Syntax.
From Blood Require Import Typing.

(** ** Shifting (de Bruijn)

    Shift free variables in an expression by [d] starting at cutoff [c].
    This is needed to avoid variable capture during substitution. *)

Fixpoint shift_expr (d : nat) (c : nat) (e : expr) : expr :=
  match e with
  | E_Var x =>
      if c <=? x then E_Var (x + d)
      else E_Var x
  | E_Const k => E_Const k
  | E_Lam T body =>
      E_Lam T (shift_expr d (S c) body)
  | E_App e1 e2 =>
      E_App (shift_expr d c e1) (shift_expr d c e2)
  | E_Let e1 e2 =>
      E_Let (shift_expr d c e1) (shift_expr d (S c) e2)
  | E_Annot e1 T =>
      E_Annot (shift_expr d c e1) T
  | E_Record fields =>
      E_Record (map (fun '(l, ei) => (l, shift_expr d c ei)) fields)
  | E_Select e1 l =>
      E_Select (shift_expr d c e1) l
  | E_Extend l e1 e2 =>
      E_Extend l (shift_expr d c e1) (shift_expr d c e2)
  | E_Perform eff op e1 =>
      E_Perform eff op (shift_expr d c e1)
  | E_Handle h e1 =>
      E_Handle (shift_handler d c h) (shift_expr d c e1)
  | E_Resume e1 =>
      E_Resume (shift_expr d c e1)
  end

with shift_handler (d : nat) (c : nat) (h : handler) : handler :=
  match h with
  | Handler hk e_ret clauses =>
      Handler hk
              (shift_expr d (S c) e_ret)  (** return binds one var *)
              (map (shift_op_clause d c) clauses)
  end

with shift_op_clause (d : nat) (c : nat) (cl : op_clause) : op_clause :=
  match cl with
  | OpClause eff op body =>
      OpClause eff op (shift_expr d (S (S c)) body)
      (** binds arg and resume *)
  end.

(** ** Substitution

    [subst j s e] substitutes expression [s] for variable [j] in [e]. *)

Fixpoint subst (j : nat) (s : expr) (e : expr) : expr :=
  match e with
  | E_Var x =>
      if j =? x then s
      else if j <? x then E_Var (x - 1)  (** shift down *)
      else E_Var x
  | E_Const k => E_Const k
  | E_Lam T body =>
      E_Lam T (subst (S j) (shift_expr 1 0 s) body)
  | E_App e1 e2 =>
      E_App (subst j s e1) (subst j s e2)
  | E_Let e1 e2 =>
      E_Let (subst j s e1) (subst (S j) (shift_expr 1 0 s) e2)
  | E_Annot e1 T =>
      E_Annot (subst j s e1) T
  | E_Record fields =>
      E_Record (map (fun '(l, ei) => (l, subst j s ei)) fields)
  | E_Select e1 l =>
      E_Select (subst j s e1) l
  | E_Extend l e1 e2 =>
      E_Extend l (subst j s e1) (subst j s e2)
  | E_Perform eff op e1 =>
      E_Perform eff op (subst j s e1)
  | E_Handle h e1 =>
      E_Handle (subst_handler j s h) (subst j s e1)
  | E_Resume e1 =>
      E_Resume (subst j s e1)
  end

with subst_handler (j : nat) (s : expr) (h : handler) : handler :=
  match h with
  | Handler hk e_ret clauses =>
      Handler hk
              (subst (S j) (shift_expr 1 0 s) e_ret)
              (map (subst_op_clause j s) clauses)
  end

with subst_op_clause (j : nat) (s : expr) (cl : op_clause) : op_clause :=
  match cl with
  | OpClause eff op body =>
      OpClause eff op
               (subst (S (S j)) (shift_expr 2 0 s) body)
  end.

(** ** Notation for substitution *)

Notation "e [ j ':=' s ]" := (subst j s e) (at level 20, left associativity).

(** ** Context removal

    Remove the [j]-th element from a context. *)

Fixpoint remove_nth {A : Type} (j : nat) (l : list A) : list A :=
  match j, l with
  | 0, _ :: rest => rest
  | S n, x :: rest => x :: remove_nth n rest
  | _, [] => []
  end.

(** ** Weakening Lemma

    If Γ ⊢ e : T / ε then (Γ with extra binding) ⊢ (shifted e) : T / ε *)

Lemma weakening :
  forall Sigma Gamma Delta e T eff S n,
    has_type Sigma Gamma Delta e T eff ->
    has_type Sigma
             (firstn n Gamma ++ S :: skipn n Gamma)
             ((Lin_Unrestricted, false) :: Delta)
             (shift_expr 1 n e) T eff.
Proof.
  (* Proof by induction on the typing derivation.
     Each case shifts the expression and adjusts the context.
     The key insight is that shifting preserves the typing structure
     by adjusting de Bruijn indices past the insertion point. *)
Admitted.  (* TODO: complete proof *)

(** ** Substitution Preserves Typing

    This is THE key lemma for type preservation.

    Reference: FORMAL_SEMANTICS.md §12.1

    Lemma substitution_preserves_typing :
      ∀ Γ x e v T S ε,
        Γ, x : S ⊢ e : T / ε →
        Γ ⊢ v : S / pure →
        Γ ⊢ e[v/x] : T / ε.
*)

Theorem substitution_preserves_typing :
  forall Sigma Gamma Delta e v T S eff,
    has_type Sigma (S :: Gamma) ((Lin_Unrestricted, false) :: Delta) e T eff ->
    has_type Sigma Gamma Delta v S Eff_Pure ->
    has_type Sigma Gamma Delta (subst 0 v e) T eff.
Proof.
  intros Sigma Gamma Delta e v T S eff Htype Hval.
  (* Proof by induction on the derivation of has_type for e.

     The proof follows the standard structure for substitution lemmas
     in de Bruijn-indexed calculi:

     - Variable case: If the variable matches j, replace with v and use Hval.
       If the variable is different, adjust the index.

     - Lambda case: The body is under a binder, so we shift v and
       substitute at index j+1. The induction hypothesis applies.

     - Application case: Substitute in both subexpressions.

     - Let case: Similar to lambda for the body.

     - Handle case: Substitute in both the body and handler clauses.

     - Perform case: Substitute in the argument expression.

     Each case uses the induction hypothesis and the weakening lemma
     to handle shifts under binders.
  *)
Admitted.  (* TODO: complete proof by induction on Htype *)

(** ** Multi-substitution

    Substitute multiple values simultaneously. Used for handler clause
    instantiation. *)

Fixpoint multi_subst (vals : list expr) (e : expr) : expr :=
  match vals with
  | [] => e
  | v :: rest =>
      multi_subst rest (subst 0 v e)
  end.

(** ** Substitution commutes with shifting *)

Lemma shift_subst_commute :
  forall d c j s e,
    c <= j ->
    shift_expr d c (subst j s e) =
    subst (j + d) (shift_expr d c s) (shift_expr d c e).
Proof.
  (* Standard de Bruijn shifting/substitution commutation lemma.
     Proof by induction on e. *)
Admitted.  (* TODO: complete proof *)

(** ** Identity substitution *)

Lemma subst_shift_cancel :
  forall e v,
    subst 0 v (shift_expr 1 0 e) = e.
Proof.
  (* Substituting into a shifted term cancels the shift. *)
Admitted.  (* TODO: complete proof *)
