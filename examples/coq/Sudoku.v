Require Import Bool.
Require Import Basic.
Require Import Heuristic.
Require Import Full.
Require Import ListEx.
Require Import Integer.
Import IntegerNotations.
Require Import EqDec.
Require Import Space.Tactics.
Require Vector.
Require Permutation.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* A sudoku solver using SpaceSearch. *)

(* We first formulate the problem in Coq, intentionally using features that
   don't make sense at the SMT level, eg heavy use of dependently typed data
   such as Fin.t and Vector.t.

   Then we write a SpaceSearch solver using constructs that do make sense at the
   Rosette level, eg, heavy use of symbolic integers. *)

Module Type BOARD.
  Parameter t : Type -> nat -> Type.
  Parameter get : forall (A : Type) n, Fin.t (n * n) -> Fin.t (n * n) -> t A n -> A.
  Parameter set : forall (A : Type) n, Fin.t (n * n) -> Fin.t (n * n) -> A -> t A n -> t A n.
End BOARD.

Module Type BOARD_UTILS.
  Include BOARD.

  Parameter row : forall A n, Fin.t (n * n) -> t A n -> Vector.t A (n * n).
  Parameter col : forall A n, Fin.t (n * n) -> t A n -> Vector.t A (n * n).
  Parameter box : forall A n, Fin.t (n * n) -> t A n -> Vector.t A (n * n).

  Parameter Forall : forall (A : Type) (P : A -> Prop) n, t A n -> Prop.
  Parameter Forall2 : forall (A B : Type) (P : A -> B -> Prop) n, t A n -> t B n -> Prop.
End BOARD_UTILS.

Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.
Arguments None {_}.
Arguments Some {_} _.

Module VectorNotations.
  Delimit Scope vector with vector.

  Notation "[ ]" := Vector.nil : vector.
  Notation "x :: y" := (Vector.cons x y) : vector.

  Open Scope vector.
End VectorNotations.
Import VectorNotations.

Module VectorEx.
  Fixpoint all_indices (n : nat) : Vector.t (Fin.t n) n :=
    match n with
    | 0%nat => Vector.nil
    | S n => Vector.cons Fin.F1 (Vector.map Fin.FS (all_indices n))
    end.

  Lemma all_indices_complete :
    forall n (x : Fin.t n), Vector.nth (all_indices n) x = x.
  Proof.
    induction x; simpl.
    - auto.
    - erewrite Vector.nth_map by eauto. congruence.
  Qed.

  Inductive Permutation (A : Type) : forall n, Vector.t A n -> Vector.t A n -> Prop :=
    perm_nil : Permutation [] []
  | perm_skip : forall (x : A) n (l l' : Vector.t A n),
                Permutation l l' -> Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) n (l : Vector.t A n),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall n (l l' l'' : Vector.t A n),
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.

  Definition forallb {A} (f : A -> bool) n (v : Vector.t A n) : bool :=
    List.forallb f (Vector.to_list v).


  Definition tabulate {A} (f : A -> A) :=
    fix rec (n : nat) (acc : A) : Vector.t A n :=
      match n with
      | 0%nat => []
      | S n => acc :: rec n (f acc)
      end.
End VectorEx.

Module FinEx.
  Fixpoint L_or_R (m : nat) : forall n, Fin.t (m + n) -> Fin.t m + Fin.t n.
    refine match m as m0 return forall n, Fin.t (m0 + n) -> Fin.t m0 + Fin.t n with
           | 0%nat => fun n x => inr x
           | S m => fun n x => Fin.caseS' x _ (inl Fin.F1)
                                      (fun x' => match L_or_R m _ x' with
                                              | inl y => inl (Fin.FS y)
                                              | inr y => inr y
                                              end)
           end.
  Defined.
  Arguments L_or_R {_ _} _.

  Fixpoint split (m : nat) : forall n, Fin.t (m * n) -> Fin.t m * Fin.t n.
    refine match m as m0 return forall n, Fin.t (m0 * n) -> Fin.t m0 * Fin.t n with
           | 0%nat => fun n x => Fin.case0 _ x
           | S m => fun n x => match L_or_R x with
                           | inl y => (Fin.F1, y)
                           | inr y => match split _ _ y with
                                     | (a, b) => (Fin.FS a, b)
                                     end
                           end
           end.
  Defined.
  Arguments split {_ _} _.
End FinEx.

Ltac nat_to_fin p n :=
  match eval compute in (Fin.of_nat (p%nat) (n%nat)) with
  | inleft ?x => exact x
  end.

Eval compute in (Fin.of_nat 5%nat 10%nat).

Eval compute in ltac:(nat_to_fin 5%nat 10%nat).

Eval compute in FinEx.split(n:=3)(m:=3) ltac:(nat_to_fin 6%nat 9%nat).

Module BoardUtils (B : BOARD) <: BOARD_UTILS.
  Include B.

  Definition row {A n} (r : Fin.t (n * n)) (b : B.t A n) : Vector.t A (n * n) :=
    Vector.map (fun c => B.get r c b) (VectorEx.all_indices (n * n)).

  Definition col {A n} (c : Fin.t (n * n)) (b : B.t A n) : Vector.t A (n * n) :=
    Vector.map (fun r => B.get r c b) (VectorEx.all_indices (n * n)).

  Definition get_box {A n} (box i : Fin.t (n * n)) (b : B.t A n) : A :=
    let '(br, bc) := FinEx.split box in
    let '(ir, ic) := FinEx.split i in
    B.get (Fin.depair br ir) (Fin.depair bc ic) b.

  Definition box {A n} (box : Fin.t (n * n)) (b : B.t A n) : Vector.t A (n * n) :=
    Vector.map (fun i => get_box box i b) (VectorEx.all_indices (n * n)).

  Definition Forall (A : Type) (P : A -> Prop) (n : nat) (b : t A n) : Prop :=
    forall r c, P (get r c b).

  Definition Forall2 (A B : Type) (P : A -> B -> Prop) (n : nat)
             (b : t A n) (b' : t B n) : Prop :=
    forall r c,
      P (get r c b) (get r c b').
End BoardUtils.

Module Board' : BOARD.
  Definition t (A : Type) (n : nat) : Type :=
    Vector.t (Vector.t A (n * n)) (n * n).

  Definition get {A n} (r c : Fin.t (n * n)) (b : t A n) : A :=
    Vector.nth (Vector.nth b r) c.

  Definition set {A n} (r c : Fin.t (n * n)) (cell : A) (b : t A n) : t A n :=
    Vector.replace b r (Vector.replace (Vector.nth b r) c cell).

End Board'.
Module Board := BoardUtils Board'.

Module CellFin.
  Definition t n := option (Fin.t n).
End CellFin.


Definition cell_less_solved_than {A} (c1 c2 : option A) :=
  match c1 with
  | None => True
  | Some x => c2 = Some x
  end.

Definition board_less_solved_than {A n} (b1 b2 : Board.t (option A) n) : Prop :=
  Board.Forall2 cell_less_solved_than b1 b2.

Module SudokuSpec.
  Definition solved_section {n} (s : Vector.t (CellFin.t (n * n)) (n * n)) :=
      VectorEx.Permutation s (Vector.map Some (VectorEx.all_indices (n * n))).

  Definition solved {n} (b : Board.t (CellFin.t (n * n)) n) :=
    forall i,
      solved_section (Board.row i b) /\
      solved_section (Board.col i b) /\
      solved_section (Board.box i b).

  Definition solution {n} (b b' : Board.t (CellFin.t (n * n)) n) :=
    solved b' /\ board_less_solved_than b b'.
End SudokuSpec.
