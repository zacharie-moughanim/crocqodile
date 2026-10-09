From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List Nat Bool.
Import ListNotations.
Require Import Autosubst.Autosubst.

(** The Q language *)

Inductive Q : Type :=
  | Var (x : var) : Q
  | Word (w : list bool) : Q
  | Letter (b : bool) : Q
  | ConsW (hd : Q) (tl : Q) : Q
  | Abs (body : {bind Q}) : Q
  | App (f : Q) (arg : Q) : Q
.

(* For autosubst substitution etc *)
Instance Ids_term : Ids Q. derive. Defined.
Instance Rename_term : Rename Q. derive. Defined.
Instance Subst_term : Subst Q. derive. Defined.
Instance SubstLemmas_term : SubstLemmas Q. derive. Qed.

(* Notations *)

Definition ε := Word [].

Declare Custom Entry Qlang.
Declare Scope Qlang_scope.
Notation "<{ e }>" := e (at level 0, e custom Qlang at level 98) : Qlang_scope.
Notation "f x .. y" := (App .. (App f x) .. y)
                  (in custom Qlang at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : Qlang_scope.
Definition Qfun := Abs.
Definition Q0  := (Letter false).
Definition Q1  := (Letter true).
Infix ":Q:" := ConsW (in custom Qlang at level 80).
(* Notation "x <= y" := (BLe x y) (in custom Qlang at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom Qlang at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom Qlang at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom Qlang at level 75, right associativity).
*)

Open Scope Qlang_scope.

Check <{ (Qfun (Var 0)) Q0 }>. 

(** Types for the Q language *)

Inductive Qtype : Type :=
  | TLetter : Qtype
  | TWord : Qtype
  | TArr (from : Qtype) (to : Qtype) : Qtype
.

(* Utf-8 notation for types *)

Definition Σ := TLetter.
Notation "Σ*" := TWord.
Notation "A '→T' B" := (TArr A B) (at level 98).

(* Typing environment, judgement *)

Definition typenv := var → option Qtype.

Notation "t∅" := (fun _ => None).

Definition typenv_enter_abs (Γ : typenv) (τ : Qtype) : typenv :=
  fun v => match v with
  | 0 => Some τ
  | S v' => Γ v'
  end.

Definition extend_partial_map {X Y} (f g : X → option Y) :=
  ∀ (x : X) (y : Y), f x = Some y → g x = Some y.
Infix "⊑" := extend_partial_map (at level 80).

Lemma extends_empty : ∀ {X Y} (f : X → option Y), t∅ ⊑ f.
Proof.
  intros X Y f x y contra. discriminate contra.
Qed.

Reserved Notation "gamma '⊢' t '⦙' tau" (at level 20, t at next level, tau at next 
level).
Inductive Qtyping : typenv → Q → Qtype → Prop :=
  | TJVar (x : var) (Γ : typenv) (τ : Qtype) :
    (Γ x = Some τ) → (Γ ⊢ (Var x) ⦙ τ)
  | TJWord (Γ : typenv) (w : list bool) : Γ ⊢ (Word w) ⦙ Σ*
  | TJLetter (Γ : typenv) (b : bool) : Γ ⊢ (Letter b) ⦙ Σ
  | TJConsW (hd : Q) (tl : Q) (Γ : typenv) :
    Γ ⊢ hd ⦙ Σ → Γ ⊢ tl ⦙ Σ* → Γ ⊢ (ConsW hd tl) ⦙ Σ*
  | TJAbs (Γ : typenv) (α β : Qtype) (body : {bind Q}) :
    (typenv_enter_abs Γ α) ⊢ body ⦙ β → Γ ⊢ Abs body ⦙ (α →T β)
  | TJApp (Γ : typenv) (α β : Qtype) (f : Q) (arg : Q) :
    Γ ⊢ f ⦙ (α →T β) → Γ ⊢ arg ⦙ α → Γ ⊢ App f arg ⦙ β
where "gamma '⊢' t '⦙' tau" := (Qtyping gamma t tau).

(* Check (fun (gamma : typenv) (t : Q) (tau : Qtype) => ( gamma ⊢ t ⦙ tau )). *)

(** Value *)

Inductive value : Q → Prop :=
  | VWord w : value (Word w)
  | VLetter b : value (Letter b)
  | VAbs body : value (Abs body)
.

Definition is_value (term : Q) :=
  match term with
  | Word _ | Letter _ | Abs _  => true
  | _ => false
  end.

Lemma is_value_refl : ∀ (t : Q), reflect (value t) (is_value t).
Proof.
  destruct t as [x | w | b | hd tl | body | f arg];
  simpl; constructor; try constructor.
  all: intro H;
    inversion H.
Qed.

(** Operational semantics *)

(* Evaluation contexts *)

Inductive QContext : Type :=
  | CHole : QContext
  | CConsWHd (Chd : QContext) (tl : Q) : QContext
  | CConsWTl (hd : Q) (Ctl : QContext) : QContext
  | CAppF (Cf : QContext) (arg : Q) : QContext
  | CAppArg (f : Q) (Carg : QContext) : QContext
.

Notation "□" := CHole.

Inductive QEvalContext : QContext → Prop :=
  | EHole : QEvalContext □
  | EConsWHd (Chd : QContext) (tl : Q) :
    QEvalContext Chd →
    QEvalContext (CConsWHd Chd tl)
  | EConsWTl (hd : Q) (Ctl : QContext) :
    value hd → 
    QEvalContext Ctl →
    QEvalContext (CConsWTl hd Ctl)
  | EAppF (Cf : QContext) (arg : Q) :
    QEvalContext Cf →
    QEvalContext (CAppF Cf arg)
  | EAppArg (f : Q) (Carg : QContext) :
    value f →
    QEvalContext Carg →
    QEvalContext (CAppArg f Carg)
.

Reserved Notation "C '⋄' u" (at level 50).
Fixpoint plug (C : QContext) (u : Q) : Q :=
  match C with
  | □ => u
  | CConsWHd Chd tl => ConsW (Chd ⋄ u) tl
  | CConsWTl hd Ctl => ConsW hd (Ctl ⋄ u)
  | CAppF Cf arg => App (Cf ⋄ u) arg
  | CAppArg f Carg => App f (Carg ⋄ u)
  end
where "C '⋄' u" := (plug C u).

Lemma plug_eq_var :
  ∀ (C : QContext) (t : Q)
  (x : var),
  C ⋄ t = Var x →
  C = □ ∧ t = Var x.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  2, 3, 4, 5: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_word :
  ∀ (C : QContext) (t : Q)
  (w : list bool),
  C ⋄ t = Word w →
  C = □ ∧ t = Word w.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  2, 3, 4, 5: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_letter :
  ∀ (C : QContext) (t : Q)
  (b : bool),
  C ⋄ t = Letter b →
  C = □ ∧ t = Letter b.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  2, 3, 4, 5: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_cons :
  ∀ (C : QContext) (t : Q)
  (hd tl : Q),
  C ⋄ t = ConsW hd tl →
  C = □ ∧ t = ConsW hd tl ∨
  (∃ Chd, C = CConsWHd Chd tl ∧ Chd ⋄ t = hd) ∨
  (∃ Ctl, C = CConsWTl hd Ctl ∧ Ctl ⋄ t = tl).
Proof.
  intros E.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  - intros t hd tl eq.
    simpl in eq.
    left.
    split. 1: reflexivity. assumption.
  - intros t hd tl' eq.
    simpl in eq.
    injection eq.
    clear eq; intros eq1 eq2.
    subst. right. left.
    exists Chd.
    split; congruence.
  - intros t hd' tl eq.
    right; right.
    exists Ctl.
    simpl in eq.
    injection eq; clear eq; intros eq1 eq2; subst.    
    split; reflexivity.
  - intros t hd tl eq.
    discriminate eq.
  - intros t hd tl eq.
    discriminate eq.
Qed.

Lemma plug_eq_abs :
  ∀ (C : QContext) (t : Q)
  (body : {bind Q}),
  C ⋄ t = Abs body →
  C = □ ∧ t = Abs body.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  2, 3, 4, 5: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_app :
  ∀ (C : QContext) (t : Q)
  (f arg : Q),
  C ⋄ t = App f arg →
  C = □ ∧ t = App f arg ∨
  (∃ Cf, C = CAppF Cf arg ∧ Cf ⋄ t = f) ∨
  (∃ Carg, C = CAppArg f Carg ∧ Carg ⋄ t = arg).
Proof.
  intros E.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg].
  - intros t hd tl eq.
    simpl in eq.
    left.
    split. 1: reflexivity. assumption.
  - intros t f arg eq.
    discriminate eq.
  - intros t f arg eq.
    discriminate eq.
  - intros t hd tl' eq.
    simpl in eq.
    injection eq.
    clear eq; intros eq1 eq2.
    subst. right. left.
    exists Cf.
    split; congruence.
  - intros t hd' tl eq.
    right; right.
    exists Carg.
    simpl in eq.
    injection eq; clear eq; intros eq1 eq2; subst.
    split; reflexivity.
Qed.

(* Small step semantics *)

Reserved Notation "t '→topQ' u" (at level 90).
Inductive toplevelStep : Q → Q → Prop :=
  | StepCons (b : bool) (w : list bool) : ConsW (Letter b) (Word w) →topQ Word (b :: w)
  | StepBetaRedex (t u : Q) :
    value u →
    App (Abs t) u →topQ t.[fun x => match x with | 0 => u | _ => Var x end]
where "t '→topQ' u" := (toplevelStep t u).

Reserved Notation "t '→Q' u" (at level 90).
Inductive step : Q → Q → Prop :=
  | StepCtx (E : QContext) (t u t' u' : Q) :
    QEvalContext E →
    t' →topQ u' →
    t = E ⋄ t' →
    u = E ⋄ u' →
    t →Q u
where "t '→Q' u" := (step t u).

Lemma step_toplevel_step : ∀ (t u : Q), t →topQ u → t →Q u.
Proof.
  intros t u H.
  assert (eqt : t = □ ⋄ t).
  reflexivity.
  assert (equ : u = □ ⋄ u).
  reflexivity.
  rewrite eqt.
  rewrite equ.
  apply (StepCtx □ t u t u).
  3, 4: reflexivity.
  - constructor.
  - assumption.
Qed.

Lemma value_normal : ∀ (t : Q), value t → (¬ ∃ u, t →Q u).
Proof.
  intros t Hval.
  inversion Hval as [ w H | b H | body H ]; intros [u contra].
  all: inversion contra as [E t' u' Hevalctx Hred eq Hredtop eq3]; subst.
  all: destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg]; simpl in eq3; try discriminate eq3.
  all: subst.
  all: inversion Hredtop.
Qed.

Lemma eval_context_value : ∀ (C : QContext) (t : Q),
  ¬ value t → QEvalContext C → ¬ value (C ⋄ t).
Proof.
  induction C as [|Chd IH tl|hd Ctl IH|Cf IH arg|f Carg IH];
  intros t Hnotval Hevalctx contra; simpl in contra.
  all: inversion contra; subst.
  all: apply Hnotval; apply contra.
Qed.

(** Operational semantics & Typing *)

Lemma typed_value : ∀ (t : Q) (τ : Qtype),
  t∅ ⊢ t ⦙ τ → value t →
    τ = Σ ∧ (∃ b, t = Letter b) ∨
    τ = Σ* ∧ (∃ w, t = Word w) ∨
    (∃ α β, τ = (α →T β)) ∧ (∃ body, t = Abs body)
  .
Proof.
  intros t τ Htyp Hval.
  inversion Hval as [w|b|body]; subst.
  - inversion Htyp as [| Γ w' eq | | | |]; subst.
    right; left.
    split.
    1: reflexivity.
    exists w. reflexivity.
  - inversion Htyp as [| | Γ b' eq | | |]; subst.
    left.
    split.
    1: reflexivity.
    exists b. reflexivity.
  - inversion Htyp as [| | | | Γ α β body' Htypbody eq1 eq2 eq3 | ]; subst.
    right; right.
    split.
    1: exists α, β; reflexivity.
    exists body.
    reflexivity.
Qed.

Lemma progress : ∀ (t : Q) (τ : Qtype),
  t∅ ⊢ t ⦙ τ → (∃ u, t →Q u) ∨ (value t).
Proof.
  intros t τ Htyp.
  remember t∅ as Γ eqn:eqgamma.
  induction Htyp as [
    x Γ' τ' eqtyp|
    Γ' w|
    Γ' b|
    hd tl Γ' Htyphd IHhd Htyptl IHtl|
    Γ' α β body Htypbody IH|
    Γ' α β f arg Htypf IHf Htyparg IHarg].
  2, 3, 5: right; constructor.
  - subst.
    discriminate eqtyp.
  - destruct IHhd as [[hd' Hhdred] | Hvalhd].
    1: assumption.
    2: destruct IHtl as [[tl' Htlred] | Hvaltl].
    + left. exists (ConsW hd' tl).
      inversion Hhdred as [Chd thd uhd thd' uhd' Hevalhd Hredhd' eq1 eq2 eq3 eq4]
      ; subst.
      apply (StepCtx (CConsWHd Chd tl) _ _ thd' uhd').
      * constructor.
        assumption.
      * assumption.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + assumption.
    + left. exists (ConsW hd tl').
      inversion Htlred as [Ctl ttl utl ttl' utl' Hevaltl Hredtl' eq1 eq2 eq3 eq4]
      ; subst.
      apply (StepCtx (CConsWTl hd Ctl) _ _ ttl' utl').
      * constructor; assumption.
      * assumption.
      * reflexivity.
      * reflexivity.
    + subst. specialize (typed_value hd Σ Htyphd Hvalhd) as [
      [_ [b eq]]|
      [[contra _]|
      [[α [β contra]] _]]
      ].
      2, 3: discriminate contra.
      subst. specialize (typed_value tl Σ* Htyptl Hvaltl) as [
      [contra _]|
      [[_ [w eq]]|
      [[α [β contra]] _]]
      ]; subst.
      1, 3: discriminate contra.
      left.
      eexists.
      apply step_toplevel_step.
      constructor.
  - subst.
    destruct IHf as [[f' Hfred] | Hfval].
    1: reflexivity.
    2: destruct IHarg as [[arg' Hargred] | Hargval].
    2: reflexivity.
    + left; exists (App f' arg).
      inversion Hfred as [Cf t u t' u' Heval' Htopred eq2 eq3 eq4]; subst.
      eapply (StepCtx (CAppF Cf arg)).
      * constructor.
        apply Heval'.
      * apply Htopred.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + left.
      inversion Hargred as [Carg t u t' u' Heval' Htopred eq2 eq3 eq4]; subst.
      exists (App f (Carg ⋄ u')).
      eapply (StepCtx (CAppArg f Carg)).
      * constructor; assumption.
      * apply Htopred.
      * simpl; reflexivity.
      * simpl; reflexivity.
    + specialize (typed_value f (α →T β) Htypf Hfval) as [
      [contra _]|[
      [contra _]|
      [[α' [β' eq']] [body' eqbody]]
      ]].
      1, 2: discriminate contra.
      subst.
      injection eq'.
      intros eq1 eq2; subst. clear eq'.
      left.
      eexists.
      eapply (StepCtx □).
      3: {
        simpl.
        reflexivity.
      }
      3: {
        simpl.
        reflexivity.
      }
      * constructor.
      * constructor. assumption.
Qed.

(* Note: restricting the following lemma to evaluation contexts ensures
  The typing environment is unchanged in every judgement appearing in it. *)
Lemma type_compositionality : ∀ (Γ : typenv) (E : QContext) (t : Q) (τ : Qtype),
  QEvalContext E →
  (Γ ⊢ (E ⋄ t) ⦙ τ) ↔
  ∃ (τ' : Qtype), (Γ ⊢ t ⦙ τ') ∧ (∀ t', Γ ⊢ t' ⦙ τ' → Γ ⊢ (E ⋄ t') ⦙ τ).
Proof.
  intros Γ E t τ Heval.
  split.
  2: {
    intros [τ' [Htyp_t Hgen]].
    apply Hgen.
    assumption.
  }
  generalize dependent Γ.
  generalize dependent t.
  generalize dependent τ.
  induction Heval as [|Chd tl Heval' IHhd|hd Ctl Hvalhd Heval' IHtl|
    Cf arg Heval' IHf|f Carg Hvalf Heval' IHarg];
  intros τ t Γ Htyp.
  - simpl in Htyp. exists τ.
    split.
    + assumption.
    + intros t' Htyp'.
      simpl.
      apply Htyp'.
  - simpl in Htyp.
    inversion Htyp as [| | | hd' tl' Γ' Htyphd Htyptl eq2 eq3 eq4 | |]; subst.
    specialize (IHhd _ _ _ Htyphd) as [τ' [Htypt Hgen]].
    exists τ'.
    split.
    + assumption.
    + intros t'' Htypt''.
      simpl.
      constructor.
      * apply Hgen. assumption.
      * assumption.
  - simpl in Htyp.
    inversion Htyp as [| | | hd' tl' Γ' Htyphd Htyptl eq2 eq3 eq4 | |]; subst.
    specialize (IHtl _ _ _ Htyptl) as [τ' [Htypt Hgen]].
    exists τ'.
    split.
    + assumption.
    + intros t'' Htypt''.
      simpl.
      constructor.
      * assumption.
      * apply Hgen.
        assumption.
  - simpl in Htyp.
    inversion Htyp as [| | | | | Γ' α β f' arg' Htypf Htyparg eq2 eq3 eq4]; subst.
    specialize (IHf _ _ _ Htypf) as [τ' [Htypt Hgen]].
    exists τ'.
    split.
    + assumption.
    + intros t'' Htypt''.
      simpl.
      econstructor.
      * apply Hgen.
        assumption.
      * assumption.
  - simpl in Htyp.
    inversion Htyp as [| | | | | Γ' α β f' arg' Htypf Htyparg eq2 eq3 eq4]; subst.
    specialize (IHarg _ _ _ Htyparg) as [τ' [Htypt Hgen]].
    exists τ'.
    split.
    + assumption.
    + intros t'' Htypt''.
      simpl.
      econstructor.
      * apply Htypf.
      * apply Hgen.
        assumption.
Qed.

Print Q.

Fixpoint list_out_abs (l : list var) : list var :=
  match l with
  | [] => []
  | 0 :: tl => list_out_abs tl
  | (S y) :: tl => y :: list_out_abs tl
  end.

Lemma In_list_out_abs : ∀ (l : list var) (x : var),
  In x (list_out_abs l) ↔ In (S x) l.
Proof.
  induction l as [|h t IH]; intros x; split; simpl.
  1, 2: intro H; assumption.
  all: intro HIn.
  - destruct h as [|h].
    + right; apply IH. assumption.
    + simpl in HIn.
      destruct HIn as [Hhd | Htl].
      * left; f_equal; assumption.
      * right; apply IH; assumption.
  - destruct h as [|h].
    + destruct HIn as [contra | Htl].
      * discriminate contra.
      * apply IH; assumption.
    + destruct HIn as [Hhd | Htl].
      * left. injection Hhd. intro H; assumption.
      * right; apply IH; assumption.
Qed.

Fixpoint freevars (t : Q) : list var := match t with
  | Var x => [x]
  | Word _ | Letter _ => []
  | ConsW hd tl => freevars hd ++ freevars tl
  | App f arg => freevars f ++ freevars arg
  | Abs body => list_out_abs (freevars body)
  end.

Definition ground : Q → Prop := λ t, freevars t = [].

Lemma typed_freevars_in_typenv : ∀ (Γ : typenv) (t : Q) (τ : Qtype),
  Γ ⊢ t ⦙ τ → (∀ (x : var), In x (freevars t) → Γ x ≠ None).
Proof.
  intros Gamma t tau Htyp.
  induction Htyp as [
    y Ξ α HΞeq |
    Ξ w |
    Ξ b |
    t1 t2 Ξ Ht1 IHt1 Ht2 IHt2 |
    Ξ α β body Hbody IHbody |
    Ξ α β t1 t2 Ht1 IHt1 Ht2 IHt2
  ]; intros x HIn.
  2, 3: exfalso; apply HIn.
  2, 4:
    simpl in HIn;
    apply in_app_or in HIn as [HIn1 | HIn2]; [
      apply IHt1; assumption |
      apply IHt2; assumption
    ].
  - destruct HIn as [Hy | contra].
    2: exfalso; assumption.
    subst.
    rewrite HΞeq.
    intro H; discriminate H.
  - simpl in HIn.
    apply In_list_out_abs in HIn.
    destruct x as [|x].
    + apply IHbody in HIn.
      unfold typenv_enter_abs in HIn.
      assumption.
    + specialize (IHbody (S (S x)) HIn).
      unfold typenv_enter_abs in IHbody.
      assumption.
Qed.

Lemma typed_emptyenv_ground : ∀ (t : Q) (τ : Qtype), t∅ ⊢ t ⦙ τ → ground t.
Proof.
  intros t τ Htyp.
  specialize (typed_freevars_in_typenv t∅ t τ Htyp) as Htypedvar.
  unfold ground.
  destruct (freevars t) as [|x fvtl].
  + reflexivity.
  + exfalso.
    apply (Htypedvar x).
    * left. reflexivity.
    * reflexivity.
Qed.

Lemma freevars_subst_eq : ∀ (t : Q) (σ : var → Q),
  (∀ (x : var), In x (freevars t) → (σ x = Var x)) →
  t.[σ] = t.
Proof.
  induction t as [
    x|
    w|
    b|
    t1 IH1 t2 IH2|
    body IHbody|
    t1 IH1 t2 IH2
  ]; intros σ Hfv.
  2, 3: reflexivity.
  2, 4: simpl;
    rewrite IH1, IH2; [reflexivity| intros x HIn;
      simpl in Hfv;
      apply Hfv;
      apply in_or_app;
      right; assumption | intros x HIn;
      simpl in Hfv;
      apply Hfv;
      apply in_or_app;
      left; assumption].
  - simpl in Hfv. specialize (Hfv x).
    simpl.
    rewrite Hfv.
    1: reflexivity.
    left; reflexivity.
  - simpl.
    rewrite IHbody.
    1: reflexivity.
    intros x HIn.
    simpl in Hfv.
    unfold up.
    unfold ".:".
    destruct x as [|x].
    + reflexivity.
    + simpl.
      rewrite Hfv.
      * simpl. reflexivity.
      * simpl. clear -HIn.
        apply In_list_out_abs. assumption.
Qed.

Lemma ground_subst_eq : ∀ (t : Q) (σ : var → Q), ground t → t.[σ] = t.
Proof.
  intros t σ Hgnd.
  apply freevars_subst_eq.
  intros x H.
  unfold ground in Hgnd.
  rewrite Hgnd in H.
  simpl in H.
  exfalso; assumption.
Qed.

Lemma type_weakening : ∀ (Γ Γ' : typenv) (t : Q) (τ : Qtype),
  Γ ⊑ Γ' → Γ ⊢ t ⦙ τ → Γ' ⊢ t ⦙ τ.
Proof.
  intros Γ Γ' t τ Hextends Htyp.
  generalize dependent Γ'.
  induction Htyp as [
    y Γ α HΓeq |
    Γ w |
    Γ b |
    t1 t2 Γ Ht1 IHt1 Ht2 IHt2 |
    Γ α β body Hbody IHbody |
    Γ α β t1 t2 Ht1 IHt1 Ht2 IHt2
  ]; intros Γ' Hextends.
  4, 6: econstructor; [apply IHt1 | apply IHt2]; assumption.
  2, 3: constructor.
  - constructor. apply Hextends. assumption.
  - constructor.
    apply IHbody.
    intros x y eq.
    unfold typenv_enter_abs in eq.
    destruct x as [|x].
    + rewrite <- eq.
      simpl. reflexivity.
    + simpl.
      apply Hextends.
      assumption.
Qed.

Lemma typing_substitution :
  ∀ (Γ Γ': typenv) (x : var) (t v : Q) (τx τ : Qtype) (σ : var → Q),
  (Γ' x = Some τx ∧ ∀ (y : var), x ≠ y → Γ y = Γ' y) (* Γ' = Γ, x : τx *) →
  (σ x = v ∧ ∀ (y : var), x ≠ y → σ y = Var y) (* σ *) →
  Γ' ⊢ t ⦙ τ →
  value v → (t∅ ⊢ v ⦙ τx) →
  Γ ⊢ t.[σ] ⦙ τ.
Proof.
  intros Γ Γ' x t v τx τ σ HΓs Hσ Htyp.
  generalize dependent Γ.
  generalize dependent τx.
  generalize dependent v.
  generalize dependent x.
  generalize dependent σ.
  induction Htyp as [
    y Ξ α HΞeq |
    Ξ w |
    Ξ b |
    t1 t2 Ξ Ht1 IHt1 Ht2 IHt2 |
    Ξ α β body Hbody IHbody |
    Ξ α β t1 t2 Ht1 IHt1 Ht2 IHt2
  ]; intros σ x v [Hσx Hσ] τx Γ [HΞx HΓs] Hval Htypv.
  4, 6: simpl; econstructor; [
    eapply IHt1; [ split; [apply Hσx | assumption] |
      split; [apply HΞx | assumption ] |
      assumption |
      assumption
    ] | 
    eapply IHt2; [
      split; [apply Hσx | assumption] |
      split; [apply HΞx | assumption] |
      assumption |
      assumption
    ]
  ].
  - destruct (x =? y) eqn:eqyx.
    + apply PeanoNat.Nat.eqb_eq in eqyx.
      subst.
      simpl.
      rewrite HΞeq in HΞx.
      injection HΞx.
      intro eq; subst.
      clear -Htypv.
      apply (type_weakening t∅).
      * apply extends_empty.
      * assumption.
    + simpl.
      apply PeanoNat.Nat.eqb_neq in eqyx.
      rewrite Hσ.
      2: assumption.
      constructor.
      rewrite HΓs.
      2: assumption.
      assumption.
  - simpl. constructor.
  - simpl. constructor.
  - simpl.
    constructor.
    eapply IHbody.
    3: apply Hval.
    3: apply Htypv.
    + split.
      Unshelve.
      3: apply (S x).
      * unfold up.
        simpl.
        rewrite Hσx.
        remember t∅ as Γ0 eqn:eqempty.
        clear -Hval Htypv eqempty.
        {
          rewrite rename_subst.
          apply ground_subst_eq.
          eapply typed_emptyenv_ground.
          subst.
          apply Htypv.
        }
      * intros y neqyx.
        unfold up.
        unfold ids.
        unfold ".:".
        unfold Ids_term.
        destruct y as [|y].
        -- reflexivity.
        -- simpl.
          rewrite Hσ.
          2: {
            congruence.
          }
          simpl.
          reflexivity.
    + split.
      * unfold typenv_enter_abs.
        assumption.
      * intros y neqSxy.
        destruct y as [|y].
        1: reflexivity.
        1: {
          simpl.
          apply HΓs.
          intro eq; rewrite eq in neqSxy.
          apply neqSxy. reflexivity.
        }
Qed.


Lemma subject_reduction : ∀ (t t' : Q) (τ : Qtype),
  t∅ ⊢ t ⦙ τ → t →Q t' → t∅ ⊢ t' ⦙ τ.
Proof.
  intros t t' τ Htyp Hred.
  inversion Hred as [E s u s' u' Heval Htopred eq1 eq2 eq3 eq4]; subst.
  apply type_compositionality in Htyp as [τ' [Htyps' Hgen]].
  2: assumption.
  apply Hgen.
  clear Heval Hred Hgen E.
  inversion Htopred as [b w eq1 eq2|body arg Hval eq2 eq3]; subst.
  - inversion Htyps'; subst.
    constructor.
  - inversion Htyps' as [| | | | |Γ' α β body' arg' Htypf Htyparg eq1 eq2]; subst.
    inversion Htypf as [| | | |Γ' α' β' body' Htypbody eq1 eq2 |]; subst.
    eapply typing_substitution.
    4: apply Hval.
    4: apply Htyparg.
    3: apply Htypbody.
    + Unshelve. 2: apply 0.
      split.
      * simpl. reflexivity.
      * intros y neqy0.
        destruct y as [|y]. 1: exfalso; apply neqy0; reflexivity.
        simpl. reflexivity.
    + simpl. split. 1: reflexivity.
      intros y neqy0.
      destruct y as [|y]. 1: exfalso; apply neqy0; reflexivity.
      reflexivity.
Qed.

(** Functions to compute steps *)

Definition compute_toplevel_step (term : Q) : option Q :=
  match term with
  | ConsW (Letter b) (Word w) =>
    Some (Word (b :: w))
  | App (Abs body) arg =>
    if is_value arg then
      Some (body.[fun x => match x with | 0 => arg | _ => Var x end])
    else
      None
  | _ => None
  end.

Definition compute_toplevel_step_refl : ∀ (t u : Q),
  (t →topQ u) ↔ compute_toplevel_step t = Some u.
Proof.
  intros t u.
  split.
  - destruct t as
    [x | w | b | hd tl | body | f arg]; intro Hred; inversion Hred as [b' w' eq1 eq2| body' eq Hval]; subst.
    + simpl. reflexivity.
    + simpl.
      specialize (reflect_iff _ _ (is_value_refl arg)) as Hrefl.
      rewrite Hrefl in Hval.
      rewrite Hval.
      reflexivity.
  - intro H.
    destruct t as
    [x | w | b | hd tl | body | f arg]; simpl in H; try discriminate H.
    + destruct hd as [x' | w' | b' | hd' tl' | body' | f' arg'];
      try discriminate H.
      destruct tl as [x'' | w'' | b'' | hd'' tl'' | body'' | f'' arg''];
      try discriminate H.
      injection H; clear H; intro eq; subst.
      constructor.
    + destruct f as [x' | w' | b' | hd' tl' | body' | f' arg'];
      try discriminate H.
      destruct (is_value arg) eqn:Hisval;
      specialize (reflect_iff _ _ (is_value_refl arg)) as Hrefl.
      * rewrite <- Hrefl in Hisval.
        injection H; clear H; intro eq; subst.
        constructor.
        assumption.
      * discriminate H.
Qed.

Definition letter_value (b : bool) : value (Letter b).
specialize (reflect_iff _ _ (is_value_refl (Letter b))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Definition word_value (w : list bool) : value (Word w).
specialize (reflect_iff _ _ (is_value_refl (Word w))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Definition abs_value (body : {bind Q}) : value (Abs body).
specialize (reflect_iff _ _ (is_value_refl (Abs body))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Fixpoint compute_eval_env (term : Q) : option (QContext * Q)%type :=
  match term with
  | ConsW hd tl =>
    if is_value hd then
      if is_value tl then
        match hd, tl with
        | Letter b, Word w => Some (□, ConsW (Letter b) (Word w))
        | _, _ => None
        end
      else
        match compute_eval_env tl with
        | None => None
        | Some (Ctl, redex) => Some (CConsWTl hd Ctl, redex)
        end
    else
      match compute_eval_env hd with
      | None => None
      | Some (Chd, redex) => Some (CConsWHd Chd tl, redex)
      end
  | App f arg =>
    if is_value f then
      if is_value arg then
        match f with
        | Abs body => Some (□, App (Abs body) arg)
        | _ => None
        end
      else
        match compute_eval_env arg with
        | None => None
        | Some (Carg, redex) => Some (CAppArg f Carg, redex)
        end
    else
      match compute_eval_env f with
      | None => None
      | Some (Cf, redex) => Some (CAppF Cf arg, redex) 
      end
  | _ => None
  end
.

Definition compute_step (term : Q) : option Q :=
  match compute_eval_env term with
  | None => None
  | Some (E, redex) =>
    match compute_toplevel_step redex with
    | None => None
    | Some reduced => Some (E ⋄ reduced)
    end
  end.

Lemma compute_eval_env_spec : ∀ (E : QContext) (t t' : Q),
  compute_eval_env t = Some (E, t') ↔ QEvalContext E ∧ t = E ⋄ t' ∧ (∃ u', t' →topQ u').
Proof.
  intros E t t'.
  split.
  - induction t as [x|b|w|hd IHhd tl IHtl|body IH|f IHf arg IHarg] in E, t' |- *;
    intro H.
    1, 2, 3, 5: simpl in H; discriminate H.
    + simpl in H.
      destruct (is_value hd) eqn:eqisvalhd.
      * destruct (is_value tl) eqn:eqisvaltl.
        -- destruct hd as [xhd|whd|bhd|hdhd tlhd|bodyhd|fhd arghd];
          try discriminate H.
          destruct tl as [xtl|wtl|btl|hdtl tltl|bodytl|ftl argtl];
          try discriminate H.
          injection H; intros eq1 eq2; subst.
          repeat split.
          ++ constructor.
          ++ exists (Word (bhd :: wtl)).
            constructor.
        -- destruct (compute_eval_env tl) as [[Etl redextl]|] eqn:eqEtl.
          ++ injection H; intros eq1 eq2; subst.
            specialize (IHtl Etl t').
            destruct IHtl as [IHtl1 [IHtl2 IHtl3]].
            1: reflexivity.
            repeat split.
            ** constructor.
              --- apply (reflect_iff _ _ (is_value_refl hd)).
                assumption.
              --- assumption.
            ** simpl. f_equal.
              assumption.
            ** assumption.
          ++ discriminate H.
      * destruct (compute_eval_env hd) as [[Ehd redexhd]|].
        2: discriminate H.
        injection H; intros eq1 eq2; subst; clear H.
        specialize (IHhd Ehd t') as [IHhd1 [IHhd2 IHhd3]].
        1: reflexivity.
        subst.
        repeat split.
        -- constructor. assumption.
        -- assumption.
    + simpl in H.
      destruct (is_value f) eqn:eqisvalf.
      * destruct (is_value arg) eqn:eqisvalarg.
        -- destruct f as [xf|wf|bf|hdf tlf|bodyf|ff argf];
          try discriminate H.
          injection H; intros eq1 eq2; subst.
          repeat split.
          ++ constructor.
          ++ eexists.
            constructor.
            apply (reflect_iff _ _ (is_value_refl arg)).
            assumption.
        -- destruct (compute_eval_env arg) as [[Earg redexarg]|] eqn:eqEarg.
          ++ injection H; intros eq1 eq2; subst.
            specialize (IHarg Earg t').
            destruct IHarg as [IHarg1 [IHarg2 IHarg3]].
            1: reflexivity.
            repeat split.
            ** constructor.
              --- apply (reflect_iff _ _ (is_value_refl f)).
                assumption.
              --- assumption.
            ** simpl. f_equal.
              assumption.
            ** assumption.
          ++ discriminate H.
      * destruct (compute_eval_env f) as [[Ef redexf]|].
        2: discriminate H.
        injection H; intros eq1 eq2; subst; clear H.
        specialize (IHf Ef t') as [IHf1 [IHf2 IHf3]].
        1: reflexivity.
        subst.
        repeat split.
        -- constructor. assumption.
        -- assumption.
  - induction E as [|Chd IH tl|hd Ctl IH|Cf IH arg|f Carg IH]
      in t, t' |-*;  intros [Heval [eq [u' Htopred]]]; subst.
    + simpl.
      inversion Htopred as [b w eq1 eq2|f arg Hvalue eq]; subst.
      * simpl.
        reflexivity.
      * simpl.
        rewrite (reflect_iff _ _ (is_value_refl arg)) in Hvalue.
        rewrite Hvalue.
        reflexivity.
    + inversion Heval as [ |G0 G1 Hevalhd | | |]; subst.
      specialize (IH (Chd ⋄ t') t').
      simpl.
      rewrite IH.
      * destruct (Chd ⋄ t') eqn:eqt;
          try reflexivity;
          try (simpl in IH; discriminate IH).
        all: (repeat split; try reflexivity; try assumption).
        all: exists u'; assumption.
      * repeat split. 1: assumption.
        exists u'. assumption.
    + inversion Heval as [ | |hd' Ctl' Hval Heval' eq | |]; subst.
      specialize (IH (Ctl ⋄ t') t').
      simpl.
      rewrite IH.
      * assert (Hisvalhd : is_value hd = true).
        {
          rewrite <- (reflect_iff _ _ (is_value_refl _)).
          assumption.
        }
        rewrite Hisvalhd.
        assert (HnotisvalCtl : is_value (Ctl ⋄ t') = false).
        {
          destruct (is_value (Ctl ⋄ t')) eqn:eqisvalC.
          + exfalso.
            eapply eval_context_value.
            2: apply Heval'.
            2: apply (reflect_iff _ _ (is_value_refl _)).
            2: apply eqisvalC.
            intro Hvalt'.
            eapply value_normal.
            * apply Hvalt'.
            * exists u'.
              apply step_toplevel_step.
              assumption.
          + reflexivity.
        }
        rewrite HnotisvalCtl.
        reflexivity.
      * repeat split.
        1: assumption.
        exists u'; assumption.
    + inversion Heval as [ | | | Cf' arg' Heval' eq1 | ]; subst.
      simpl.
      rewrite (IH (Cf ⋄ t') t').
      * destruct Cf as [| Chd' tl' | hd' Ctl' | Cf' arg' | f' Carg' ];
        simpl; try reflexivity.
        destruct t' as [x|w|b|hd tl|body|f'' arg''] eqn:eqt'; try reflexivity.
        all: exfalso.
        all: apply (value_normal t').
        all: try (rewrite eqt'; constructor).
        all: exists u'; rewrite eqt'; apply step_toplevel_step; assumption.
      * repeat split.
        -- assumption.
        -- exists u'.
          assumption.
    + inversion Heval as [ | | | | f' Carg' Hvalue Heval' eq]; subst.
      simpl.
      rewrite (IH (Carg ⋄ t') t').
      * assert (Hisvalf : is_value f = true).
        {
          rewrite <- (reflect_iff _ _ (is_value_refl _)).
          assumption.
        }
        rewrite Hisvalf.
        assert (HnotisvalCarg : is_value (Carg ⋄ t') = false).
        {
          destruct (is_value (Carg ⋄ t')) eqn:eqisvalC.
          + exfalso.
            eapply eval_context_value.
            2: apply Heval'.
            2: apply (reflect_iff _ _ (is_value_refl _)).
            2: apply eqisvalC.
            intro Hvalt'.
            eapply value_normal.
            * apply Hvalt'.
            * exists u'.
              apply step_toplevel_step.
              assumption.
          + reflexivity.
        }
        rewrite HnotisvalCarg.
        reflexivity.
      * repeat split.
        -- assumption.
        -- exists u'.
          assumption.
Qed.


Definition compute_step_refl : ∀ (t u : Q),
  (t →Q u) ↔ compute_step t = Some u.
Proof.
  intros t u.
  split.
  - intro Hred.
    inversion Hred as [E t0 u0 t' u' Heval Hredtop eq1 eq2]; subst.
    specialize (compute_eval_env_spec E (E ⋄ t') t') as [_ Heval_env].
    unfold compute_step.
    rewrite Heval_env.
    2: {
      repeat split. 1: assumption.
      exists u'.
      assumption.
    }
    specialize (compute_toplevel_step_refl t' u') as [Hcompute_toplevel _].
    apply Hcompute_toplevel in Hredtop as eq_compute_toplevel.
    rewrite eq_compute_toplevel.
    reflexivity.
  - intro H.
    destruct (compute_eval_env t) eqn:eq_evalenv_t.
    + destruct p as [E t'].
      unfold compute_step in H.
      rewrite eq_evalenv_t in H.
      apply compute_eval_env_spec in eq_evalenv_t as [Heval [eq [u' Hredtop]]]; subst.
      apply (compute_toplevel_step_refl t' u') in Hredtop as eq_toplevel_step.
      rewrite eq_toplevel_step in H.
      injection H; clear H; intro H; subst.
      econstructor.
      * apply Heval.
      * apply Hredtop.
      * reflexivity.
      * reflexivity.
    + unfold compute_step in H.
      rewrite eq_evalenv_t in H.
      discriminate H.
Qed.   

Fixpoint compute_fuel (term : Q) (fuel : nat) : Q :=
  match fuel with
  | 0 => term
  | S fuel' => 
    match compute_step term with
    | None => term
    | Some term' => compute_fuel term' fuel'
    end
  end.

Definition IdLetter := Abs (Var 0).

(* Compute (compute_fuel <{ IdLetter IdLetter IdLetter }> 3). *)