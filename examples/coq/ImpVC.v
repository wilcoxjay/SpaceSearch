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

Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* An automatic Hoare-style program verifier for Imp. *)

(* Outline of this file:
   - [module exp] syntax of expressions and denotational semantics to both Z and Int
   - [module cmd] syntax of commands and [Module step] small-step operational semantics over Z
   - [module hoare] definition of the Hoare triple for partial correctness
   - [functions wp and vc] a VC generator
   - [hoare_space] a SpaceSearch Space for counterexamples to VCs with admitted soundness theorem
*)

(* TODO:
   - connect the VC to the Coq-level Hoare triple to prove soundness
   - extract and try it!
   - integrate with street fighting Imp material
*)

Module ty.
  Inductive t :=
  | Int
  | Bool
  .

  Definition denote I (ty : t) : Type :=
    match ty with
    | Int => I
    | Bool => bool
    end.
End ty.

Module member.
  Inductive t A (x : A) : list A -> Type :=
  | Here : forall l, t x (x :: l)
  | There : forall y l, t x l -> t x (y :: l)
  .
  Arguments Here {_ _ _}.
  Arguments There {_ _ _ _} _.

  Definition case_nil {A} {a : A} (P : t a [] -> Type) (m : t a []) : P m :=
    match m with end.

  Definition case_cons {A} {a : A} (P : forall h tl, t a (h :: tl) -> Type)
             (here : forall l, P a l Here) (there : forall h tl (m : t a tl), P h tl (There m))
             {h tl} (m : t a (h :: tl)) : P h tl m :=
    match m with
    | Here => here _
    | There m' => there _ _ m'
    end.
End member.

Module hlist.
  Inductive t A (B : A -> Type) : list A -> Type :=
  | nil : t B []
  | cons : forall a l, B a -> t B l -> t B (a :: l)
  .
  Arguments nil {_ _}.
  Arguments cons {_ _ _ _} _ _.

  Definition case_nil {A} {B : A -> Type} (P : t B [] -> Type) (case : P nil) hl : P hl :=
    match hl with
    | nil => case
    end.

  Definition case_cons {A} {B : A -> Type} {h tl} (P : t B (h :: tl) -> Type)
             (case : forall hh ht, P (cons hh ht))
             (hl : t B (h :: tl)) : P hl :=
    match hl with
    | cons hh ht => fun P' case' => case' hh ht
    end P case.

  Definition head {A} {B : A -> Type} {a : A} {l} (h : t B (a :: l)) : B a :=
    match h with
    | cons b _ => b
    end.

  Definition tail {A} {B : A -> Type} {a : A} {l} (h : hlist.t B (a :: l)) : hlist.t B l :=
    match h with
    | cons _ t => t
    end.

  Fixpoint get {A} {B : A -> Type} {l} (h : t B l) (x : A) {struct h} : member.t x l -> B x :=
    match h with
    | nil => member.case_nil _
    | cons b h' => fun m =>
        member.case_cons _ (fun _ b' _ => b') (fun _ _ m' _ rec => rec m') m b (get h')
    end.
  Arguments get {A B l} h {x} m.

  Fixpoint set {A} {B : A -> Type} {l} (x : A) (m : member.t x l) (y : B x) :
    t B l -> t B l :=
    match m with
    | member.Here => case_cons _ (fun _ h' => cons y h')
    | member.There m' => fun h => case_cons _ (fun y0 h' rec => cons y0 (rec h')) h (set m' y)
    end.
  Arguments set {A B l} {x} m y h.

  Definition map A {B C : A -> Type} (f : forall {a}, B a -> C a) : forall l, t B l -> t C l :=
    fix go {l} (h : t B l) : t C l :=
      match h with
      | nil => nil
      | cons b h => cons (f b) (go h)
      end.

  Fixpoint identity A (l : list A) : t (fun x => member.t x l) l :=
    match l as l0 return t (fun x => member.t _ l0) l0 with
    | [] => nil
    | x :: l => cons member.Here (map (fun y m => member.There m) (identity l))
    end.
End hlist.

Module op.
  Inductive t : list ty.t -> ty.t -> Type :=
  | ZConst : Z -> t [] ty.Int
  | BConst : bool -> t [] ty.Bool
  | Plus : t [ty.Int; ty.Int] ty.Int
  | Eq : forall ty, t [ty; ty] ty.Bool
  | Le : t [ty.Int; ty.Int] ty.Bool
  | And : t [ty.Bool; ty.Bool] ty.Bool
  | Or : t [ty.Bool; ty.Bool] ty.Bool
  | Implies : t [ty.Bool; ty.Bool] ty.Bool
  | Not : t [ty.Bool] ty.Bool
  .

  Definition Z_denote l ty (o : op.t l ty) : hlist.t (ty.denote Z) l -> ty.denote Z ty :=
    match o with
    | ZConst z => fun _ => z
    | BConst b => fun _ => b
    | Plus => fun h => Z.add (hlist.head h) (hlist.head (hlist.tail h))
    | Eq ty =>
      match ty with
      | ty.Int => fun h => Z.eqb (hlist.head h) (hlist.head (hlist.tail h))
      | ty.Bool => fun h => Bool.eqb (hlist.head h) (hlist.head (hlist.tail h))
      end
    | Le => fun h => Z.leb (hlist.head h) (hlist.head (hlist.tail h))
    | And => fun h => andb (hlist.head h) (hlist.head (hlist.tail h))
    | Or => fun h => orb (hlist.head h) (hlist.head (hlist.tail h))
    | Implies => fun h => implb (hlist.head h) (hlist.head (hlist.tail h))
    | Not => fun h => negb (hlist.head h)
    end.

  Section int.
    Context {BAS:Basic}.
    Context {INT:@Integer BAS}.

    Definition int_denote l ty (o : op.t l ty) : hlist.t (ty.denote Int) l -> ty.denote Int ty :=
      match o with
      | ZConst z => fun _ => fromZ z
      | BConst b => fun _ => b
      | Plus => fun h => Integer.plus (hlist.head h) (hlist.head (hlist.tail h))
      | Eq ty =>
        match ty with
        | ty.Int => fun h => Integer.equal (hlist.head h) (hlist.head (hlist.tail h))
        | ty.Bool => fun h => Bool.eqb (hlist.head h) (hlist.head (hlist.tail h))
        end
      | Le => fun h => Integer.le (hlist.head h) (hlist.head (hlist.tail h))
      | And => fun h => andb (hlist.head h) (hlist.head (hlist.tail h))
      | Or => fun h => orb (hlist.head h) (hlist.head (hlist.tail h))
      | Implies => fun h => implb (hlist.head h) (hlist.head (hlist.tail h))
      | Not => fun h => negb (hlist.head h)
      end.
  End int.
End op.

Module exp.
  Local Unset Elimination Schemes.
  Inductive t (G : list ty.t) : ty.t -> Type :=
  | Var : forall ty, member.t ty G -> t G ty
  | Op : forall l ty, op.t l ty -> hlist.t (t G) l -> t G ty
  .

  Definition lift0 {ty G} (op : op.t [] ty) : t G _ :=
    Op op hlist.nil.

  Definition ZConst {G} z : t G _ := lift0 (op.ZConst z).
  Definition BConst {G} b : t G _ := lift0 (op.BConst b).

  Definition lift1 {ty1 ty G} (op : op.t [ty1] ty) e1 : t G _:=
    Op op (hlist.cons e1 hlist.nil).

  Definition Not {G} : _ -> t G _ := lift1 op.Not.

  Definition lift2 {ty1 ty2 ty G} (op : op.t [ty1; ty2] ty) e1 e2 : t G _:=
    Op op (hlist.cons e1 (hlist.cons e2 hlist.nil)).

  Definition Plus {G} : _ -> _ -> t G _ := lift2 op.Plus.
  Definition Eq {G ty} : _ -> _ -> t G _ := lift2 (op.Eq ty).
  Definition Le {G} : _ -> _ -> t G _ := lift2 op.Le.
  Definition And {G} : _ -> _ -> t G _ := lift2 op.And.
  Definition Or {G} : _ -> _ -> t G _ := lift2 op.Or.
  Definition Implies {G} : _ -> _ -> t G _ := lift2 op.Implies.

  Definition subst' {G} (env : hlist.t (t G) G) : forall ty, t G ty -> t G ty :=
    fix go ty e :=
      match e in t _ ty0 return t _ ty0 with
      | Var m => hlist.get env m
      | Op o h => Op o (hlist.map go h)
      end.

  Definition subst {G ty} (e : t G ty) {ty'} (from : member.t ty' G) (to : t G ty') : t G ty :=
    subst' (hlist.set from to (hlist.map (fun _ m => Var m) (hlist.identity G))) e.

  Definition denote {G I} (env : hlist.t (ty.denote I) G)
             (op_denote : forall l ty, op.t l ty -> hlist.t (ty.denote I) l -> ty.denote I ty) :
    forall ty, t G ty -> ty.denote I ty :=
    fix go ty (e : t G ty) : ty.denote I ty :=
       match e with
       | Var m => hlist.get env m
       | Op o h => op_denote _ _ o (hlist.map go h)
       end.

  Definition Z_denote {G ty} (env : hlist.t (ty.denote Z) G) (e : t G ty) : ty.denote Z ty :=
    denote env (@op.Z_denote) e.

  Section int.
    Context {BAS:Basic}.
    Context {INT:@Integer BAS}.

    Definition int_denote {G ty} (env : hlist.t (ty.denote Int) G) (e : t G ty)
      : ty.denote Int ty :=
      denote env (@op.int_denote _ _) e.
  End int.
End exp.

Module cmd.
  Inductive t (G : list ty.t) :=
  | Skip
  | Assign : forall ty, member.t ty G -> exp.t G ty -> t G
  | Seq : t G -> t G -> t G
  | If : exp.t G ty.Bool -> t G -> t G -> t G
  | While : exp.t G ty.Bool -> exp.t G ty.Bool -> t G -> t G
  .
  Arguments Skip {_}.
End cmd.

Module step.
  Notation env G := (hlist.t (ty.denote Z) G).

  Inductive t {G} : env G -> cmd.t G -> env G -> cmd.t G -> Prop :=
  | Assign : forall ty E m e, t E (cmd.Assign(ty:=ty) m e)
                           (hlist.set m (exp.Z_denote E e) E) cmd.Skip
  | Seq : forall E E' c1 c1' c2,
      t E c1 E' c1' ->
      t E (cmd.Seq c1 c2) E' (cmd.Seq c1' c2)
  | SeqSkip : forall E c,
      t E (cmd.Seq cmd.Skip c) E c
  | If : forall E e c1 c2,
      t E (cmd.If e c1 c2) E (if exp.Z_denote E e then c1 else c2)
  | While : forall E e Inv c,
      t E (cmd.While e Inv c) E (if exp.Z_denote E e then cmd.Skip
                                 else cmd.Seq c (cmd.While e Inv c))
  .

  Module star.
    Inductive t {G} : env G -> cmd.t G -> env G -> cmd.t G -> Prop :=
    | Refl : forall E c, t E c E c
    | Step : forall E1 c1 E2 c2 E3 c3,
        step.t E1 c1 E2 c2 ->
        t E2 c2 E3 c3 ->
        t E1 c1 E3 c3
    .
  End star.
End step.

Module hoare.
  Definition t {G} (P : exp.t G ty.Bool) (c : cmd.t G) (Q : exp.t G ty.Bool) : Prop :=
    forall E E',
      exp.Z_denote E P = true ->
      step.star.t E c E' cmd.Skip ->
      exp.Z_denote E Q = true.
End hoare.

(* See https://courses.cs.washington.edu/courses/cse507/17wi/lectures/vcg.rkt *)
Fixpoint wp {G} (c : cmd.t G) (Q : exp.t G ty.Bool) : exp.t G ty.Bool :=
  match c with
  | cmd.Skip => Q
  | cmd.Assign m e => exp.subst Q m e
  | cmd.Seq c1 c2 => wp c1 (wp c2 Q)
  | cmd.If e c1 c2 => exp.And (exp.Implies e (wp c1 Q))
                         (exp.Implies (exp.Not e) (wp c2 Q))
  | cmd.While b Inv c => Inv
  end.

Fixpoint vc {G} (c : cmd.t G) (Q : exp.t G ty.Bool) : exp.t G ty.Bool :=
  match c with
  | cmd.Skip => exp.BConst true
  | cmd.Assign m e => exp.BConst true
  | cmd.Seq c1 c2 => exp.And (vc c1 (wp c2 Q)) (vc c2 Q)
  | cmd.If e c1 c2 => exp.And (vc c1 Q) (vc c2 Q)
  | cmd.While b Inv c =>
    exp.And (exp.Implies (exp.And Inv b) (wp c Inv))
   (exp.And (vc c Inv)
            (exp.Implies (exp.And Inv (exp.Not b)) Q))
  end.

Definition spec_exp {G} P c Q : exp.t G ty.Bool :=
  exp.And (vc c Q)
          (exp.Implies P (wp c Q)).

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

Section full_hlist.
  Context {BAS:Basic}.
  Variable (A : Type) (B : A -> Type).
  Context `{forall x : A, Full (B x)}.

  Fixpoint full_hlist (l : list A) : Space (hlist.t B l) :=
    match l as l0 return Space (hlist.t B l0) with
    | [] => single hlist.nil
    | x :: l =>
      bind full (fun y : B x =>
      bind (full_hlist l) (fun h =>
      single (hlist.cons y h)))
    end.

  Lemma denote_full_hlist_ok : forall l, denote (full_hlist l) = Full_set (hlist.t B l).
  Proof.
    intros l.
    apply Extensionality_Ensembles'.
    intros h.
    rewrite fullIsTrue. intuition. clear H0.
    revert h.
    induction l; simpl; intros.
    - destruct h using hlist.case_nil.
      space_crush.
    - destruct h using hlist.case_cons.
      space_crush.
      exists hh.
      split; try constructor.
      space_crush.
      exists h.
      split; auto.
      space_crush.
  Qed.

  Global Instance fullHlist l : Full (hlist.t B l) :=
    {| full := full_hlist l;
       denoteFullOk := denote_full_hlist_ok l
    |}.
End full_hlist.

Section space.
  Context {BAS:Basic}.
  Context {INT:@Integer BAS}.

  Definition full_ty (ty : ty.t) : Space (ty.denote Int ty) :=
    match ty with
    | ty.Int => full
    | ty.Bool => full
    end.

  Lemma full_ty_ok : forall ty, denote (full_ty ty) = Full_set (ty.denote Int ty).
  Proof.
    unfold full_ty.
    destruct ty; space_crush.
  Qed.

  Instance fullTy ty : Full (ty.denote Int ty) :=
    {| full := full_ty ty;
       denoteFullOk := full_ty_ok ty |}.

  Definition hoare_space {G} P (c : cmd.t G) Q : Space (hlist.t (ty.denote Int) G) :=
    bind full (guard (fun env => exp.int_denote env (spec_exp P c Q))).

  Theorem hoare_space_sound :
    forall G P (c : cmd.t G) Q,
      denote (hoare_space P c Q) = Empty_set _ ->
      hoare.t P c Q.
  Admitted.

  (* Not sure about completeness. *)
End space.
