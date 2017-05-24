Require Import Bool.
Require Import Basic.
Require Import Heuristic.
Require Import Full.
Require Import ListEx.
Require Import Integer.
Import IntegerNotations.
Require Import EnsemblesEx.
Import EnsembleNotations.
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

  Fixpoint vector_option_traverse {A n} (v : Vector.t (option A) n) : option (Vector.t A n) :=
    match v  with
    | [] => Some []
    | o :: v =>
      match o with
      | None => None
      | Some x =>
        match vector_option_traverse v with
        | None => None
        | Some v => Some (x :: v)
        end
      end
    end.

  Definition filled_and {A} (pred : forall {n}, Vector.t A n -> bool)
             {m} (v : Vector.t (option A) m) : bool :=
    match vector_option_traverse v with
    | None => false
    | Some v => pred v
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

(* TODO: move this into library. *)
Section SpaceEx.
  Context {BAS:Basic}.
  Context {SEA:@Search BAS}.
  Context {INT:@Integer BAS}.

  Definition guard {A} (p : A -> bool) (a : A) : Space A :=
    if p a then single a else empty.

  Lemma denoteGuardOk : forall A (p : A -> bool) (a : A),
      denote (guard p a) = if p a then denote (single a) else denote empty.
  Proof.
    unfold guard.
    intros.
    break_if; auto.
  Qed.
End SpaceEx.
(* Must go outside of section. Hints do not survive sections. *)
Hint Rewrite @denoteGuardOk : space.

Section Sudoku.
  Context {BAS:Basic}.
  Context {SEA:@Search BAS}.
  Context {INT:@Integer BAS}.

  Notation cell := (option Int).

  Definition vdistinct {n} (v : Vector.t Int n) : bool :=
    distinct (Vector.to_list v).

  Definition vinrange {n} (v : Vector.t Int n) : bool :=
    VectorEx.forallb (fun x => (zero <=? x) && (x <? Integer.fromZ (Z.of_nat n)))%int v.

  Definition solved_section {n} (section : Vector.t cell (n * n)) : bool :=
    VectorEx.filled_and (fun _ v => vdistinct v && vinrange v) section.

  Definition solved {n} (b : Board.t cell n) : bool :=
    VectorEx.forallb (fun i =>
        solved_section (Board.row i b) &&
        solved_section (Board.col i b) &&
        solved_section (Board.box i b))
      (VectorEx.all_indices _).

  Definition mvfold_left {A B} (f : A -> B -> Space B) {n} (v : Vector.t A n) (b : B) : Space B :=
    Vector.fold_left (fun b a => bind b (fun b => f a b)) (single b) v.

  Definition mboard_fold_2d {n}
             (f : Fin.t (n * n) -> Fin.t (n * n) -> Board.t cell n -> Space (Board.t cell n))
             (b : Board.t cell n) : Space (Board.t cell n) :=
    mvfold_left
      (fun r b => mvfold_left (fun c b => f r c b) (VectorEx.all_indices _) b)
      (VectorEx.all_indices _)
      b.

  Definition all_boards_more_solved_than {n} (b : Board.t cell n) : Space (Board.t cell n) :=
    mboard_fold_2d
      (fun r c b =>
         match Board.get r c b with
         | None => bind full (fun x : Int => single (Board.set r c (Some x) b))
         | Some _ => single b
         end)
      b.

  Definition sudoku_space {n} (b : Board.t cell n) : Space (Board.t cell n) :=
    bind
      (all_boards_more_solved_than b)
      (guard solved).

  Definition index_rel {n} (i : Fin.t n) (i' : Int) : Prop :=
    Integer.fromZ (Z.of_nat (S (proj1_sig (Fin.to_nat i)))) = i'.

  Definition cell_rel {n} (c : CellFin.t n) (c' : cell) : Prop :=
    match c, c' with
    | None, None => True
    | Some i, Some i' => index_rel i i'
    | _, _ => False
    end.

  Definition section_rel n (v : Vector.t (CellFin.t n) n) (v' : Vector.t cell n) : Prop :=
    Vector.Forall2 cell_rel v v'.

  Definition board_rel {n} (b : Board.t (CellFin.t (n * n)) n) (b' : Board.t cell n) : Prop :=
    Board.Forall2 cell_rel b b'.

  Lemma mboard_fold_2d_inv :
    forall n f P,
      (forall r c b1 b2,
          P b1 ->
          b2 ∈ denote (f r c b1) ->
          P b2) ->
      forall b1 b2,
        P b1 ->
        b2 ∈ denote (mboard_fold_2d(n:=n) f b1) ->
        P b2.
  Admitted.

  Lemma cell_less_solved_than_refl :
    forall A (c : option A), cell_less_solved_than c c.
  Proof.
    unfold cell_less_solved_than.
    destruct c; auto.
  Qed.

  Lemma board_less_solved_than_refl:
    forall A n (b : Board.t (option A) n), board_less_solved_than b b.
  Proof.
    unfold board_less_solved_than, Board.Forall2.
    auto using cell_less_solved_than_refl.
  Qed.

  Lemma board_less_solved_than_trans :
    forall A n (b1 b2 b3 : Board.t (option A) n),
      board_less_solved_than b1 b2 ->
      board_less_solved_than b2 b3 ->
      board_less_solved_than b1 b3.
  Admitted.

  Lemma board_less_solved_than_set :
    forall A n (b : Board.t (option A) n) (c : option A) i j,
      cell_less_solved_than (Board.get i j b) c ->
      board_less_solved_than b (Board.set i j c b).
  Admitted.

  Lemma all_boards_more_solved_than_sound :
    forall n b1 b2,
      b2 ∈ denote (all_boards_more_solved_than(n:=n) b1) ->
      board_less_solved_than b1 b2.
  Proof.
    unfold all_boards_more_solved_than.
    intros n b1 b2.
    apply mboard_fold_2d_inv.
    - clear b2. intros r c b2 b3 Lt In.
      break_match; space_crush.
      eapply board_less_solved_than_trans; [eauto|].
      apply board_less_solved_than_set.
      rewrite Heqo.
      exact I.
    - auto using board_less_solved_than_refl.
  Qed.

  Definition cell_in_range (n : nat) (c : cell) : Prop :=
    match c with
    | None => True
    | Some i => 0 <= ⟦ i ⟧ < Z.of_nat n
    end.

  Definition board_in_range {n} (b : Board.t cell n) :=
    Board.Forall (cell_in_range (n * n)) b.

  Lemma board_in_range_rel_surjective :
    forall n b',
      board_in_range(n:=n) b' ->
      exists b, board_rel b b'.
  Admitted.

  Lemma forallb_cons :
    forall A (p : A -> bool) n (h : A) (t : Vector.t A n),
      VectorEx.forallb p (h :: t) =
      p h && VectorEx.forallb p t.
  Proof. reflexivity. Qed.

  Lemma forallb_Forall :
    forall A (p : A -> bool) n (v : Vector.t A n),
      VectorEx.forallb p v = true ->
      Vector.Forall (fun x => p x = true) v.
  Proof.
    induction v; simpl; intros.
    - constructor.
    - rewrite forallb_cons in H.
      do_bool. intuition.
      constructor; auto.
  Qed.

  Lemma Forall_case_cons :
    forall A (P : A -> Prop) n (Q : A -> Vector.t A n -> Prop),
      (forall h t, P h -> Vector.Forall P t -> Q h t) ->
      forall h (t : Vector.t A n),
        Vector.Forall P (h :: t) -> Q h t.
  Proof.
    intros A P n Q HQ h t H.
    revert Q HQ.
    refine match H in Vector.Forall _ v0 return match v0 return Prop with
                                                | Vector.nil => True
                                                | Vector.cons h0 t0 => forall (Q : _ -> _ -> Prop), _ -> Q h0 t0
                                                end with
           | Vector.Forall_nil _ => I
           | Vector.Forall_cons _ _ _ _ _ => _
           end.
    intros.
    auto.
  Qed.

  Lemma Forall_map :
    forall A B (f : A -> B) (P : B -> Prop) n (v : Vector.t A n),
      Vector.Forall P (Vector.map f v) ->
      Vector.Forall (fun a => P (f a)) v.
  Proof.
    induction v; simpl; intros.
    - constructor.
    - remember (Vector.map f v) as y. revert Heqy.
      remember (f h) as x. revert Heqx.
      revert x y H IHv.
      refine (@Forall_case_cons _ _ _ _ _); intros. subst.
      constructor; auto.
  Qed.

  Lemma Forall_all_indices_forall :
    forall n P,
      Vector.Forall P (VectorEx.all_indices n) ->
      forall x, P x.
  Proof.
    induction n; simpl; intros.
    - destruct x using Fin.case0.
    - remember Fin.F1 as h. revert Heqh.
      remember (Vector.map _ _) as t. revert Heqt.
      revert h t H.
      refine (@Forall_case_cons _ _ _ _ _).
      intros. subst.
      destruct x using Fin.caseS'; auto.
      + apply Forall_map in H0.
        eapply IHn in H0.
        eauto.
  Qed.


  Lemma vector_option_traverse_Some_Forall :
    forall A P n (v : Vector.t (option A) n) v',
      VectorEx.vector_option_traverse v = Some v' ->
      Vector.Forall P v' ->
      Vector.Forall (fun o => match o with
                           | Some x => P x
                           | None => False
                           end) v.
  Admitted.

  Lemma Forall_implies :
    forall A (P Q : A -> Prop) n v,
      Vector.Forall(n:=n) P v ->
      (forall a, P a -> Q a) ->
      Vector.Forall Q v.
  Proof.
    induction 1; intros; constructor; auto.
  Qed.

  Lemma solved_section_row_board_in_range :
    forall n v,
      solved_section(n:=n) v = true ->
      Vector.Forall (cell_in_range (n * n)) v.
  Proof.
    unfold solved_section.
    intros n v H.
    unfold VectorEx.filled_and in *.
    break_match; try discriminate.
    rewrite andb_true_iff in H.
    destruct H as [_ H].
    unfold vinrange in H.
    apply forallb_Forall in H.
    eapply vector_option_traverse_Some_Forall in H; eauto.
    eapply Forall_implies; eauto.
    simpl. intros.
    break_match; try contradiction.
    space_crush.
    firstorder.
  Qed.

  Lemma solved_board_in_range :
    forall n (b : Board.t cell n),
      solved b = true ->
      board_in_range b.
  Proof.
    intros n b H r c.
    unfold solved in *.
    apply forallb_Forall in H.
    apply Forall_all_indices_forall with (x := r) in H .
    rewrite !andb_true_iff in H.
    destruct H as [[H _] _].
    apply solved_section_row_board_in_range in H.
    unfold Board.row in H.
    apply Forall_map in H.
    apply Forall_all_indices_forall with (x := c) in H.
    auto.
  Qed.

  Lemma board_rel_row_rel :
    forall n b b' r,
      board_rel(n:=n) b b' ->
      section_rel (Board.row r b) (Board.row r b').
  Admitted.

  Lemma board_rel_col_rel :
    forall n b b' r,
      board_rel(n:=n) b b' ->
      section_rel (Board.col r b) (Board.col r b').
  Admitted.

  Lemma board_rel_box_rel :
    forall n b b' r,
      board_rel(n:=n) b b' ->
      section_rel (Board.box r b) (Board.box r b').
  Admitted.

  Lemma Permutation_list :
    forall A n (v1 v2 : Vector.t A n),
      Permutation.Permutation (Vector.to_list v1) (Vector.to_list v2) ->
      VectorEx.Permutation v1 v2.
  Admitted.


  Definition vCountUp (n : nat) (start : Int) : Vector.t Int n :=
    VectorEx.tabulate (plus one) n start.

  Lemma all_indices_index_rel :
    forall n,
      Vector.Forall2 index_rel (VectorEx.all_indices (n * n)) (vCountUp (n * n) one).
  Admitted.

  Lemma solved_section_sound :
    forall n v v',
      section_rel v v' ->
      solved_section(n:=n) v' = true ->
      SudokuSpec.solved_section v.
  Proof.
    unfold solved_section, VectorEx.filled_and, SudokuSpec.solved_section.
    intros.
    break_match; try discriminate.
    do_bool.
  Admitted.

  Lemma solved_sound :
    forall n b2 b2',
      board_rel(n:=n) b2 b2' ->
      solved b2' = true ->
      SudokuSpec.solved b2.
  Proof.
    unfold solved, SudokuSpec.solved.
    intros n b2 b2' Rel Solved i.
    apply forallb_Forall in Solved.
    apply Forall_all_indices_forall with (x := i) in Solved.
    do_bool.
    intuition eauto using solved_section_sound, board_rel_row_rel,
                          board_rel_col_rel, board_rel_box_rel.
  Qed.

  Lemma board_less_solved_than_lift :
    forall n b1 b2 b1' b2',
      board_rel(n:=n) b1 b1' ->
      board_rel(n:=n) b2 b2' ->
      board_less_solved_than b1' b2' ->
      board_less_solved_than b1 b2.
  Admitted.

  Lemma sudoku_space_sound :
    forall n b1 b1',
      board_rel(n:=n) b1 b1' ->
      forall b2',
        b2' ∈ denote (sudoku_space b1') ->
        exists b2, board_rel b2 b2' /\
              SudokuSpec.solution b1 b2.
  Proof.
    unfold sudoku_space.
    intros.
    space_crush.
    break_if; space_crush.
    pose proof (solved_board_in_range _ Heqb) as Range.
    pose proof board_in_range_rel_surjective Range as Rel.
    destruct Rel as [b2 Rel].
    exists b2. split; auto.
    red.
    split.
    - eauto using solved_sound.
    - eauto using all_boards_more_solved_than_sound, board_less_solved_than_lift.
  Qed.
End Sudoku.
