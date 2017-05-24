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
Require Import Program.
Require Import Classical.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* An automatic Hoare-style program verifier for Imp. *)

(* Outline of this file:
   - syntax of expressions and denotational semantics to both Z and Int (module `exp`)
   - syntax of commands (module `cmd`) and small-step operational semantics over Z (module `step`)
   - definition of the Hoare triple for partial correctness (module `hoare`)
   - a VC generator (functions `wp` and `vc`)
   - a SpaceSearch Space for counterexamples to VCs with soundness theorem (`hoare_space`)
*)

(* TODO:
   - cleanup vc_wp_sound
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

  Definition denote_map {I1 I2} (f : I1 -> I2) {ty} : ty.denote I1 ty ->  ty.denote I2 ty :=
    match ty with
    | Int => f
    | Bool => fun x => x
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

  Lemma get_map : forall A (B C : A -> Type) (f : forall a, B a -> C a) l x (m: member.t x l) h,
      get (map f h) m =
      f _ (get h m).
  Proof.
    intros A B C f l x m h.
    revert m.
    induction h; simpl; intros.
    - destruct m using member.case_nil.
    - destruct a, l, m using member.case_cons; simpl; auto.
  Qed.

  Lemma map_set : forall A (B C : A -> Type) (f : forall a, B a -> C a)
                    l x (m : member.t x l) (y : B x) (h : t B l),
      map f (set m y h) = set m (f _ y) (map f h).
  Proof.
    induction h; simpl.
    - destruct m using member.case_nil.
    - destruct a, l, m using member.case_cons; simpl; f_equal; auto.
  Qed.

  Lemma map_map : forall A (B C D : A -> Type)
                    (f : forall a, B a -> C a) (g : forall a, C a -> D a)
                    l (h : t B l),
      map g (map f h) = map (fun _ y => g _ (f _ y)) h.
  Proof.
    induction h; simpl; intros.
    - auto.
    - f_equal. auto.
  Qed.

  Lemma map_ext : forall A (B C : A -> Type) (f g : forall a, B a -> C a),
      (forall a (b : B a), f a b = g a b) ->
      forall l (h : hlist.t B l),
        map f h = map g h.
  Proof.
    induction h; simpl; f_equal; auto.
  Qed.

  Fixpoint identity A (l : list A) : t (fun x => member.t x l) l :=
    match l as l0 return t (fun x => member.t _ l0) l0 with
    | [] => nil
    | x :: l => cons member.Here (map (fun y m => member.There m) (identity l))
    end.

  Lemma map_get_identity :
    forall A (B : A -> Type) l (h : hlist.t B l),
      map (fun _ x => get h x) (identity l) = h.
  Proof.
    induction h; simpl.
    - auto.
    - rewrite map_map. simpl. f_equal; auto.
  Qed.
End hlist.

Module op.
  Inductive t : list ty.t -> ty.t -> Type :=
  | ZConst : Z -> t [] ty.Int
  | BConst : bool -> t [] ty.Bool
  | Plus : t [ty.Int; ty.Int] ty.Int
  | Eq : forall ty, t [ty; ty] ty.Bool
  | Le : t [ty.Int; ty.Int] ty.Bool
  | Lt : t [ty.Int; ty.Int] ty.Bool
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
    | Lt => fun h => Z.ltb (hlist.head h) (hlist.head (hlist.tail h))
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
      | Lt => fun h => Integer.lt (hlist.head h) (hlist.head (hlist.tail h))
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

  Section rect.
    Variable G : list ty.t.
    Variable P : forall ty : ty.t, t G ty -> Type.
    Variable Ph : forall l, hlist.t (t G) l -> Type.

    Hypothesis HVar : forall ty (m : member.t ty G), P (Var m).
    Hypothesis HOp : forall l ty (o : op.t l ty) (h : hlist.t (t G) l), Ph h -> P (Op o h).

    Hypothesis Hnil : Ph hlist.nil.
    Hypothesis Hcons : forall ty l (e : t G ty) (h : hlist.t (t G) l),
        P e -> Ph h -> Ph (hlist.cons e h).

    Fixpoint rect ty (e : t G ty) : P e :=
      let fix go_hlist {l} (h : hlist.t (t G) l) : Ph h :=
          match h with
          | hlist.nil => Hnil
          | hlist.cons e h => Hcons (rect e) (go_hlist h)
          end
      in match e with
         | Var m => HVar m
         | Op o h => HOp o (go_hlist h)
         end.

    Definition rect_hlist :=
      fix go_hlist {l} (h : hlist.t (t G) l) : Ph h :=
        match h with
        | hlist.nil => Hnil
        | hlist.cons e h => Hcons (rect e) (go_hlist h)
        end.

    Definition rect_and :
      (forall ty (e : t G ty), P e) *
      (forall l (h : hlist.t (t G) l), Ph h) :=
      (@rect, @rect_hlist).
  End rect.

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
  Definition Lt {G} : _ -> _ -> t G _ := lift2 op.Lt.
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

  Lemma denote_subst' :
    forall G I (env : hlist.t (ty.denote I) G) op_denote env' ty (e : exp.t G ty),
      denote env op_denote (subst' env' e) =
      denote (hlist.map (fun _ x => denote env op_denote x) env') op_denote e.
  Proof.
    intros G I env op_denote env' ty e.
    induction ty, e using rect
    with (Ph := fun l h =>
      hlist.map (fun _ x => denote env op_denote x)
                (hlist.map (fun _ x => subst' env' x) h) =
      hlist.map (fun _ x =>
        denote (hlist.map (fun _ x => denote env op_denote x) env') op_denote x) h); simpl.
    - now rewrite hlist.get_map.
    - f_equal. auto.
    - auto.
    - f_equal; auto.
  Qed.

  Lemma denote_subst_set :
    forall I op_denote G (env : hlist.t (ty.denote I) G) ty
      (e : exp.t G ty) ty' (from : member.t ty' G) to,
      exp.denote env op_denote (exp.subst e from to) =
      exp.denote (hlist.set from (exp.denote env op_denote to) env) op_denote e.
  Proof.
    intros.
    unfold subst.
    rewrite denote_subst', hlist.map_set, hlist.map_map.
    rewrite hlist.map_ext with (g := fun _ x => hlist.get env x) by auto.
    now rewrite hlist.map_get_identity.
  Qed.

  Lemma denote_ty_denote_map :
    forall G I1 I2 (f : I1 -> I2) E
      (o1 : forall l ty, op.t l ty -> hlist.t (ty.denote I1) l -> ty.denote I1 ty)
      (o2 : forall l ty, op.t l ty -> hlist.t (ty.denote I2) l -> ty.denote I2 ty),
      (forall l ty (o : op.t l ty) (h : hlist.t (ty.denote I1) l),
          ty.denote_map f (o1 l ty o h) =
          o2 l ty o (hlist.map (fun _ e => ty.denote_map f e) h)) ->
      forall ty (e : exp.t G ty),
        exp.denote (hlist.map (fun _ x => ty.denote_map f x) E) o2 e =
        ty.denote_map f (exp.denote E o1 e).
  Proof.
    intros G I1 I2 f E o1 o2 H ty e.
    induction ty, e using rect
    with (Ph := fun l h =>
      hlist.map (@exp.denote _ _ (hlist.map (fun _ x => ty.denote_map f x) E) o2) h =
      hlist.map (fun _ e => ty.denote_map f (exp.denote E o1 e)) h); simpl.
    - apply hlist.get_map.
    - now rewrite IHe, H, hlist.map_map.
    - auto.
    - f_equal; auto.
  Qed.

  Definition Z_denote {G ty} (env : hlist.t (ty.denote Z) G) (e : t G ty) : ty.denote Z ty :=
    denote env (@op.Z_denote) e.

  Lemma Z_denote_subst_set :
    forall G (env : hlist.t (ty.denote Z) G) ty
      (e : exp.t G ty) ty' (from : member.t ty' G) to,
      Z_denote env (exp.subst e from to) =
      Z_denote (hlist.set from (Z_denote env to) env) e.
  Proof.
    intros.
    apply denote_subst_set.
  Qed.

  Section int.
    Context {BAS:Basic}.
    Context {INT:@Integer BAS}.

    Definition int_denote {G ty} (env : hlist.t (ty.denote Int) G) (e : t G ty)
      : ty.denote Int ty :=
      denote env (@op.int_denote _ _) e.

    Lemma int_denote_Z_denote :
      forall G E ty (e : exp.t G ty),
        int_denote (hlist.map (fun _ x => ty.denote_map fromZ x) E) e =
        ty.denote_map fromZ (Z_denote E e).
    Proof.
      intros.
      apply denote_ty_denote_map.
      destruct o; intros;
        repeat match goal with
               | [ H : hlist.t _ [] |- _ ] => destruct H using hlist.case_nil
               | [ H : hlist.t _ (_ :: _) |- _ ] => destruct H using hlist.case_cons
               end; simpl; auto.
      - apply denoteInjective. space_crush.
      - destruct ty0; simpl; space_crush.
      - space_crush.
      - space_crush.
    Qed.

    Lemma int_denote_Z_denote_bool :
      forall G E (e : exp.t G ty.Bool),
        int_denote (hlist.map (fun _ x => ty.denote_map fromZ x) E) e =
        Z_denote E e.
    Proof.
      intros.
      rewrite int_denote_Z_denote.
      auto.
    Qed.
  End int.
End exp.

Module cmd.
  Inductive t (G : list ty.t) :=
  | Skip
  | Assign ty (m : member.t ty G) (e : exp.t G ty)
  | Seq (c1 c2 : t G)
  | If (e : exp.t G ty.Bool) (c1 c2 : t G)
  | While (e : exp.t G ty.Bool) (Inv : exp.t G ty.Bool) (c : t G)
  .
  Arguments Skip {_}.
End cmd.

Module eval.
  Notation env G := (hlist.t (ty.denote Z) G).

  Inductive t {G} : env G -> cmd.t G -> env G -> Prop :=
  | Skip : forall E, t E cmd.Skip E
  | Assign : forall ty E m e, t E (cmd.Assign(ty:=ty) m e) (hlist.set m (exp.Z_denote E e) E)
  | Seq : forall E0 E1 E2 c1 c2,
      t E0 c1 E1 ->
      t E1 c2 E2 ->
      t E0 (cmd.Seq c1 c2) E2
  | If : forall E E' e c1 c2,
      t E (if exp.Z_denote(ty:=ty.Bool) E e then c1 else c2) E' ->
      t E (cmd.If e c1 c2) E'
  | WhileTrue : forall E1 E2 E3 e Inv c,
      exp.Z_denote(ty:=ty.Bool) E1 e = true ->
      t E1 c E2 ->
      t E2 (cmd.While e Inv c) E3 ->
      t E1 (cmd.While e Inv c) E3
  | WhileFalse : forall E e Inv c,
      exp.Z_denote(ty:=ty.Bool) E e = false ->
      t E (cmd.While e Inv c) E
  .
End eval.

Definition pred {G} (P : exp.t G ty.Bool) := (fun E => exp.Z_denote E P = true).

Module hoare.
  Definition t {G} (E : hlist.t (ty.denote Z) G) (c : cmd.t G) (Q : hlist.t (ty.denote Z) G -> Prop) : Prop :=
    forall E',
      eval.t E c E' ->
      Q E'.

  Lemma consequence : forall G E (Q Q' : _ -> Prop) c,
      hoare.t(G:=G) E c Q' ->
      (forall E, Q' E -> Q E) ->
      hoare.t(G:=G) E c Q.
  Proof.
    firstorder.
  Qed.

  Lemma Skip : forall G (P : _ -> Prop) E,
      P E ->
      hoare.t(G:=G) E cmd.Skip P.
  Proof.
    unfold hoare.t.
    intros.
    invc H0.
    auto.
  Qed.

  Lemma Assign :
    forall G E (Q : hlist.t (ty.denote Z) G -> Prop) ty (m : member.t ty G) e,
      Q (hlist.set m (exp.Z_denote E e) E) ->
      hoare.t E (cmd.Assign m e) Q.
  Proof.
    unfold hoare.t.
    intros.
    dependent destruction H0.
    auto.
  Qed.

  Lemma Seq : forall G (E : hlist.t (ty.denote Z) G) c1 c2 Q,
      hoare.t E c1 (fun E' => hoare.t E' c2 Q) ->
      hoare.t E (cmd.Seq c1 c2) Q.
  Proof.
    unfold hoare.t.
    intros.
    invc H0.
    eauto.
  Qed.

  Lemma If : forall G (E : hlist.t (ty.denote Z) G) (e : exp.t G ty.Bool) c1 c2 Q,
      (if exp.Z_denote E e then hoare.t E c1 Q else hoare.t E c2 Q) ->
      hoare.t E (cmd.If e c1 c2) Q.
  Proof.
    unfold hoare.t.
    intros.
    invc H0.
    break_if; auto.
  Qed.

  Lemma While : forall G E e (Inv : exp.t G ty.Bool) c,
      pred Inv E ->
      (forall E0, pred e E0 /\ pred Inv E0 -> hoare.t E0 c (pred Inv)) ->
      hoare.t(G:=G) E (cmd.While e Inv c) (fun E => pred (exp.Not e) E /\ pred Inv E).
  Proof.
    unfold hoare.t.
    intros.
    remember (cmd.While e Inv c) as x.
    revert e Inv c Heqx H H0.
    induction H1; intros; subst; try discriminate.
    - invc Heqx.
      eauto.
    - invc Heqx.
      unfold pred. simpl. do_bool. auto.
  Qed.
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

Lemma pred_and_iff :
  forall G (P Q : exp.t G ty.Bool) E,
    pred (exp.And P Q) E <->
    pred P E /\ pred Q E.
Proof.
  intros.
  unfold pred in *.
  simpl in *. do_bool. intuition.
Qed.

Lemma pred_implies_iff :
  forall G (P Q : exp.t G ty.Bool) E,
    pred (exp.Implies P Q) E <->
    (pred P E -> pred Q E).
Proof.
  intros.
  unfold pred in *.
  simpl in *. do_bool. intuition.
Qed.


Lemma vc_wp_sound :
  forall G (c : cmd.t G)E (Q : exp.t G ty.Bool),
    (forall E, pred (vc c Q) E) ->
    exp.Z_denote E (wp c Q) = true ->
    hoare.t E c (pred Q).
Proof.
  induction c; simpl; intros E Q VC WP;
    repeat first [setoid_rewrite @pred_and_iff in VC|
                  setoid_rewrite @pred_implies_iff in VC].
  - apply hoare.Skip.
    auto.
  - apply hoare.Assign.
    rewrite @exp.Z_denote_subst_set in *.
    auto.
  - apply hoare.Seq.
    eapply hoare.consequence.
    + apply IHc1; eauto.
      apply VC.
    + intros E0 WP2.
      apply IHc2; auto.
      apply VC.
  - apply hoare.If.
    do_bool.
    intuition.
    break_if.
    + apply IHc1; auto.
      apply VC.
    + apply IHc2; auto.
      apply VC.
  - eapply hoare.consequence.
    + apply hoare.While; auto.
      intros E0 He P.
      apply IHc; auto.
      * apply VC.
      * apply VC.
        intuition.
    + simpl.
      intros E0 He.
      apply VC.
      intuition.
Qed.

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

  Definition spec_exp {G} P c Q : exp.t G ty.Bool :=
    exp.And (vc c Q)
            (exp.Implies P (wp c Q)).

  Definition hoare_space {G} P (c : cmd.t G) Q : Space (hlist.t (ty.denote Int) G) :=
    bind full (guard (fun env => negb (exp.int_denote env (spec_exp P c Q)))).


  Theorem hoare_space_vc_wp :
    forall G P (c : cmd.t G) Q,
      (forall E, E ∈ ⟦ hoare_space P c Q ⟧ -> False) ->
      forall E, exp.Z_denote E (vc c Q) = true /\
           exp.Z_denote E (exp.Implies P (wp c Q)) = true.
  Proof.
    intros G P c Q H E.
    set (E' := (hlist.map (fun _ x => ty.denote_map fromZ x) E)).
    specialize (H E').

    unfold hoare_space in *.
    space_crush.
    simpl in H.

    pose proof (not_ex_all_not _ _ H). clear H. rename H0 into H.
    specialize (H E').
    simpl in H.
    space_crush.
    apply not_and_or in H.
    destruct H.
    - contradiction H. constructor.
    - simpl. break_if.
      + do_bool. contradiction H. constructor.
      + do_bool.
        subst E'.
        rewrite !exp.int_denote_Z_denote in Heqb.
        intuition.
  Qed.

  Theorem hoare_space_sound :
    forall G P (c : cmd.t G) Q,
      (forall E, E ∈ ⟦ hoare_space P c Q ⟧ -> False) ->
      (forall E, pred P E -> hoare.t E c (pred Q)).
  Proof.
    unfold hoare_space.
    intros G P c Q H.
    pose proof (hoare_space_vc_wp _ _ _ H) as VCWP. clear H.

    intros E HP.
    destruct (VCWP E) as [VC WP].

    apply vc_wp_sound.
    - intros E0.
      destruct (VCWP E0) as [VC0 WP0].
      auto.
    - simpl in WP. do_bool. auto.
  Qed.

  (* Not sure about completeness. *)
End space.

Section search.
  Context {BAS:Basic}.
  Context {INT:@Integer BAS}.
  Context {SEA:@Search BAS}.

  Definition prove {G} P (c : cmd.t G) Q : Result (hlist.t (ty.denote Int) G) :=
    search (hoare_space P c Q).
End search.

Require Import Rosette.Quantified.

Definition impVCRosette {G} := prove(G:=G).

Extraction Language Scheme.

(*
(define S0
  (WHILE (< x n) {<= x n}
    (:= x (+ x 1))))

(define P0 (<= x n))
(define Q0 (>= x n))
*)

Notation X := (exp.Var member.Here).
Notation N := (exp.Var (member.There member.Here)).

Definition env0 := [ty.Int; ty.Int].
Definition S0 : cmd.t env0 :=
  cmd.While (exp.Lt X N) (exp.Le X N)
    (cmd.Assign member.Here (exp.Plus X (exp.ZConst 1))).

Definition P0 : exp.t env0 ty.Bool :=
  exp.Le X N.

Definition Q0 : exp.t env0 ty.Bool :=
  exp.Le N X.

Extraction "impvc" impVCRosette env0 S0 P0 Q0.

