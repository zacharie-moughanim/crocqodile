From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List Nat Bool.
Import ListNotations.
Require Export Autosubst.Autosubst.

(** The Q language *)

Inductive Q : Type :=
  | Var (x : var) : Q
  | Word (w : list bool) : Q
  | Letter (b : bool) : Q
  | ConsW (hd : Q) (tl : Q) : Q
  | Abs (body : {bind Q}) : Q
  | App (f : Q) (arg : Q) : Q
  | IfLetter (cond : Q) (thenBody : Q) (elseBody : Q) : Q
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
Infix ":Q:" := ConsW (at level 199) : Qlang_scope.
Notation "'Qif' x 'Qthen' y 'Qelse' z" := (IfLetter x y z) (at level 90) : Qlang_scope.
(* Notation "x <= y" := (BLe x y) (in custom Qlang at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom Qlang at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom Qlang at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom Qlang at level 75, right associativity).
*)

Open Scope Qlang_scope.

Check <{ (Qfun (Qif (Var 0) Qthen (Var 0) :Q: ε Qelse ε)) Q0 }>.   

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
  | TJIf (Γ : typenv) (α : Qtype) (cond thenBody elseBody : Q) :
    Γ ⊢ cond ⦙ TLetter → Γ ⊢ thenBody ⦙ α → Γ ⊢ elseBody ⦙ α →
    Γ ⊢ (Qif cond Qthen thenBody Qelse elseBody) ⦙ α
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
  destruct t as [x | w | b | hd tl | body | f arg | cond thenBody elseBody];
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
  | CIfCond (CCond : QContext) (thenBody elseBody : Q) : QContext
  | CIfThen (cond : Q) (CThen : QContext) (elseBody : Q) : QContext
  | CIfElse (cond : Q) (thenBody : Q) (CElse : QContext) : QContext
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
  | EIfCond (CCond : QContext) (thenBody elseBody : Q) :
    QEvalContext CCond →
    QEvalContext (CIfCond CCond thenBody elseBody)
  | EIfThen (cond : Q) (CThen : QContext) (elseBody : Q) :
    value cond →
    QEvalContext CThen →
    QEvalContext (CIfThen cond CThen elseBody)
  | EIfElse (cond : Q) (thenBody : Q) (CElse : QContext) :
    value cond →
    value thenBody →
    QEvalContext CElse →
    QEvalContext (CIfElse cond thenBody CElse)
.

Reserved Notation "C '⋄' u" (at level 50).
Fixpoint plug (C : QContext) (u : Q) : Q :=
  match C with
  | □ => u
  | CConsWHd Chd tl => ConsW (Chd ⋄ u) tl
  | CConsWTl hd Ctl => ConsW hd (Ctl ⋄ u)
  | CAppF Cf arg => App (Cf ⋄ u) arg
  | CAppArg f Carg => App f (Carg ⋄ u)
  | CIfCond CCond thenBody elseBody => IfLetter (CCond ⋄ u) thenBody elseBody
  | CIfThen cond CThen elseBody => IfLetter cond (CThen ⋄ u) elseBody
  | CIfElse cond thenBody CElse => IfLetter cond thenBody (CElse ⋄ u)
  end
where "C '⋄' u" := (plug C u).

Lemma plug_eq_var :
  ∀ (C : QContext) (t : Q)
  (x : var),
  C ⋄ t = Var x →
  C = □ ∧ t = Var x.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  2, 3, 4, 5, 6, 7, 8: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_word :
  ∀ (C : QContext) (t : Q)
  (w : list bool),
  C ⋄ t = Word w →
  C = □ ∧ t = Word w.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  2, 3, 4, 5, 6, 7, 8: simpl in eq; discriminate eq.
  simpl in eq; split; congruence.
Qed.

Lemma plug_eq_letter :
  ∀ (C : QContext) (t : Q)
  (b : bool),
  C ⋄ t = Letter b →
  C = □ ∧ t = Letter b.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  2, 3, 4, 5, 6, 7, 8: simpl in eq; discriminate eq.
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
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  8, 7, 6, 5, 4: intros t hd tl eq; discriminate eq.
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
Qed.

Lemma plug_eq_abs :
  ∀ (C : QContext) (t : Q)
  (body : {bind Q}),
  C ⋄ t = Abs body →
  C = □ ∧ t = Abs body.
Proof.
  intros E t x eq.
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  2, 3, 4, 5, 6, 7, 8: simpl in eq; discriminate eq.
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
  destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse].
  2, 3, 6, 7, 8: intros t f arg eq; discriminate eq.
  - intros t hd tl eq.
    simpl in eq.
    left.
    split. 1: reflexivity. assumption.
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
  | StepIfThen (thenBody elseBody : Q) :
    value elseBody → value thenBody →
    (Qif (Letter true) Qthen thenBody Qelse elseBody) →topQ thenBody
  | StepIfElse (thenBody elseBody : Q) :
    value elseBody → value thenBody →
    (Qif (Letter false) Qthen thenBody Qelse elseBody) →topQ elseBody
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
  all: destruct E as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse]; simpl in eq3; try discriminate eq3.
  all: subst.
  all: inversion Hredtop.
Qed.

Lemma eval_context_value : ∀ (C : QContext) (t : Q),
  ¬ value t → QEvalContext C → ¬ value (C ⋄ t).
Proof.
  induction C as [|Chd tl|hd Ctl|Cf arg|f Carg|
    Ccond thenBody elseBody|cond CThen elseBody|cond thenBody CElse];
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
  - inversion Htyp as [| Γ w' eq | | | | |]; subst.
    right; left.
    split.
    1: reflexivity.
    exists w. reflexivity.
  - inversion Htyp as [| | Γ b' eq | | | |]; subst.
    left.
    split.
    1: reflexivity.
    exists b. reflexivity.
  - inversion Htyp as [| | | | Γ α β body' Htypbody eq1 eq2 eq3 | |]; subst.
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
    Γ' α β f arg Htypf IHf Htyparg IHarg|
    Γ' α cond thenBody elseBody Htypcond IHcond Htypthen IHthen Htypelse IHelse].
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
    (* toplevel reduction *)
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
  - subst. left.
    destruct IHcond as [[cond' Hcondred] | Hcondval].
    3: destruct IHthen as [[thenBody' Hthenred]|Hvalthen].
    5: destruct IHelse as [[elseBody' Helsered]|Hvalelse].
    1, 3, 5: reflexivity.
    + exists (Qif cond' Qthen thenBody Qelse elseBody).
      inversion Hcondred as [Econd t u t' u' Heval' Htopred eq1 eq2 eq3 eq4]; subst.
      eapply (StepCtx (CIfCond Econd thenBody elseBody)).
      * constructor. assumption.
      * apply Htopred.
      * simpl.
        reflexivity.
      * simpl. reflexivity.
    + exists (Qif cond Qthen thenBody' Qelse elseBody).
      inversion Hthenred as [Ethen t u t' u' Heval' Htopred eq1 eq2 eq3 eq4]; subst.
      eapply (StepCtx (CIfThen cond Ethen elseBody)).
      * constructor; assumption.
      * apply Htopred.
      * simpl.
        reflexivity.
      * simpl. reflexivity.
    + exists (Qif cond Qthen thenBody Qelse elseBody').
      inversion Helsered as [Eelse t u t' u' Heval' Htopred eq1 eq2 eq3 eq4]; subst.
      eapply (StepCtx (CIfElse cond thenBody Eelse)).
      * constructor; assumption.
      * apply Htopred.
      * simpl.
        reflexivity.
      * simpl. reflexivity.
    (* toplevel reduction *)
    + specialize (typed_value cond _ Htypcond Hcondval) as [
      [eq [[|] eq']]|[
      [contra _]|
      [[α' [β' contra]] _]
      ]]; subst;
      [eexists; apply step_toplevel_step; constructor; assumption |
       eexists; apply step_toplevel_step; constructor; assumption |
       discriminate contra |
       discriminate contra].
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
  induction Heval as [|
    Chd tl Heval' IHhd|
    hd Ctl Hvalhd Heval' IHtl|
    Cf arg Heval' IHf|
    f Carg Hvalf Heval' IHarg|
    Ccond thenBody elseBody Heval' IHcond|
    cond Cthen elseBody Hvalcond Heval' IHthen|
    cond thenBody Celse Hvalcond Hvalthen Heval' IHelse];
  intros τ t Γ Htyp.
  - simpl in Htyp. exists τ.
    split.
    + assumption.
    + intros t' Htyp'.
      simpl.
      apply Htyp'.
  - simpl in Htyp.
    inversion Htyp as [| | | hd' tl' Γ' Htyphd Htyptl eq2 eq3 eq4 | | |]; subst.
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
    inversion Htyp as [| | | hd' tl' Γ' Htyphd Htyptl eq2 eq3 eq4 | | |]; subst.
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
    inversion Htyp as [| | | | | Γ' α β f' arg' Htypf Htyparg eq2 eq3 eq4 |]; subst.
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
    inversion Htyp as [| | | | | Γ' α β f' arg' Htypf Htyparg eq2 eq3 eq4 |]; subst.
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
  - simpl in Htyp.
    inversion Htyp as [| | | | | |
    Γ' α cond' thenBody' elseBody' Htypcond' Htypthen' Htypelse' eq2 eq3 eq4]
    ; subst.
    specialize (IHcond TLetter t Γ Htypcond') as [τ' [Htyp' Hgen]].
    exists τ'.
    split; [assumption|].
    intros t' Htyp''.
    simpl.
    constructor; [apply Hgen; assumption | assumption | assumption].
  - simpl in Htyp.
    inversion Htyp as [| | | | | |
    Γ' α cond' thenBody' elseBody' Htypcond' Htypthen' Htypelse' eq2 eq3 eq4]
    ; subst.
    specialize (IHthen τ t Γ Htypthen') as [τ' [Htyp' Hgen]].
    exists τ'.
    split; [assumption|].
    intros t' Htyp''.
    simpl.
    constructor; [ assumption | apply Hgen;assumption | assumption].
  - simpl in Htyp.
    inversion Htyp as [| | | | | |
    Γ' α cond' thenBody' elseBody' Htypcond' Htypthen' Htypelse' eq2 eq3 eq4]
    ; subst.
    specialize (IHelse τ t Γ Htypelse') as [τ' [Htyp' Hgen]].
    exists τ'.
    split; [assumption|].
    intros t' Htyp''.
    simpl.
    constructor; [assumption | assumption | apply Hgen; assumption].    
Qed.

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
  | Qif cond Qthen thenBody Qelse elseBody =>
    freevars cond ++ freevars thenBody ++ freevars elseBody 
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
    Ξ α β t1 t2 Ht1 IHt1 Ht2 IHt2|
    Ξ α cond thenBody elseBody Hcond IHcond Hthen IHthen Helse IHelse
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
  - simpl in HIn.
    apply in_app_or in HIn as [HIn1 | HIn]; [
      apply IHcond ; assumption |
      apply in_app_or in HIn as [HIn2 | HIn3];
      [
        apply IHthen; assumption |
        apply IHelse; assumption
      ]
    ].
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
    t1 IH1 t2 IH2|
    t1 IH1 t2 IH2 t3 IH3
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
  - simpl.
    rewrite IH1, IH2, IH3.
    1: reflexivity.
    + intros x Hvars.
      apply Hfv.
      simpl.
      apply in_or_app; right; apply in_or_app; right; assumption.
    + intros x Hvars.
      apply Hfv.
      simpl.
      apply in_or_app; right; apply in_or_app; left; assumption.
    + intros x Hvars.
      apply Hfv.
      simpl.
      apply in_or_app; left; assumption.
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
    Γ α β t1 t2 Ht1 IHt1 Ht2 IHt2|
    Γ α cond thenBody elseBody Hcond IHcond Hthen IHthen Helse IHelse
  ]; intros Γ' Hextends.
  (* direct base cases *)
  2, 3: constructor.
  (* straightforward IH application *)
  2, 4: econstructor; [apply IHt1 | apply IHt2]; assumption.
  3: econstructor; [apply IHcond | apply IHthen | apply IHelse]; assumption.
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
    Ξ α β t1 t2 Ht1 IHt1 Ht2 IHt2|
    Ξ α cond thenBody elseBody Hcond IHcond Hthen IHthen Helse IHelse
  ]; intros σ x v [Hσx Hσ] τx Γ [HΞx HΓs] Hval Htypv.
  (* straightforward IH application *)
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
  5: { (* TODO minimize *)
    simpl. econstructor; [eapply IHcond | eapply IHthen | eapply IHelse ].
    - split.
      + apply Hσx.
      + assumption.
    - split.
      + apply HΞx.
      + assumption.
    - assumption.
    - assumption.
    - split.
      + apply Hσx.
      + assumption.
    - split.
      + apply HΞx.
      + assumption.
    - assumption.
    - assumption.
    - split.
      + apply Hσx.
      + assumption.
    - split.
      + apply HΞx.
      + assumption.
    - assumption.
    - assumption.
  }
  (* rest *)
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
  inversion Htopred as [b w eq1 eq2|body arg Hval eq2 eq3|
  cond thenBody elseBody Hval eq2| cond thenBody elseBody Hval eq2]; subst.
  - inversion Htyps'; subst.
    constructor.
  - inversion Htyps' as [| | | | |Γ' α β body' arg' Htypf Htyparg eq1 eq2| ]; subst.
    inversion Htypf as [| | | |Γ' α' β' body' Htypbody eq1 eq2 | |]; subst.
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
  - inversion Htyps' as [| | | | | |
    Γ' α cond' thenBody' elseBody' Htypcond' Htypthen' Htypelse' eq2 eq3 eq4]; subst.
    assumption.
  - inversion Htyps' as [| | | | | |
    Γ' α cond' thenBody' elseBody' Htypcond' Htypthen' Htypelse' eq2 eq3 eq4]; subst.
    assumption.
Qed.
