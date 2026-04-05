import Ctic.Functor
import Ctic.Limit

namespace CTIC.TT

inductive Lit where
  | unit
  | num (x : Nat)
  | str (x : String)
deriving Inhabited, Repr, DecidableEq

inductive Term : Nat → Type where
  | var {n} (i : Fin n) : Term n
  | lam : Term (n + 1) → Term n -- Γ. x : X ⊢ y : Y  ===>  Γ ⊢ λx.y : X → Y
  | app (x y : Term n) : Term n
  | lit (lit : Lit) : Term n
deriving Repr, DecidableEq

abbrev Rename (n m : Nat) := Fin n → Fin m

def Rename.lift : Rename n m → Rename (n + 1) (m + 1) := fun ρ i =>
  if h : i = 0 then
    ⟨0, by simp⟩
  else
    Fin.succ (ρ (i.pred h))

@[simp]
theorem Rename.lift_id : Rename.lift (n := n) id = id := by
  funext x
  simp [Rename.lift]
  intro h
  rw [h]

@[simp]
theorem Rename.lift_comp {f : Fin u → Fin v} {g : Fin v → Fin w}
    : Rename.lift (g ∘ f) = Rename.lift g ∘ Rename.lift f := by
  funext x
  simp [Rename.lift]
  split
  . split
    . simp
    . rename_i h1 h2
      exfalso
      apply h2
      intro h3
      exfalso
      apply h3 h1
  . split
    . rename_i h1 h2
      have := h2 h1
      simp [Fin.succ_ne_zero] at this
    . rename_i h1 h2
      congr

def rename (ρ : Rename n m) : Term n → Term m
  | .var i => .var (ρ i)
  | .lam t => .lam (rename ρ.lift t)
  | .app x y => .app (rename ρ x) (rename ρ y)
  | .lit x => .lit x

abbrev Subst (n m : Nat) := Fin n → Term m

def Subst.lift : Subst n m → Subst (n + 1) (m + 1) := fun σ i =>
  if h : i = 0 then
    Term.var 0
  else
    rename Fin.succ (σ (i.pred h))

@[simp]
theorem Subst.lift_var {n : Nat} : Subst.lift (n := n) Term.var = Term.var := by
  funext i
  simp [Subst.lift]
  split
  . rename_i h
    simp [h]
  . simp [rename]

@[simp]
theorem Subst.lift_on_zero : Subst.lift σ 0 = Term.var 0 := by
  simp [Subst.lift]

def subst (σ : Subst n m) : Term n → Term m
  | .var i => σ i
  | .lam t => .lam (subst σ.lift t)
  | .app x y => .app (subst σ x) (subst σ y)
  | .lit x => .lit x

@[simp]
theorem rename_succ {i : Fin u} : rename Fin.succ (Term.var i) = Term.var (Fin.succ i) := by
  simp [rename]

@[simp]
theorem rename_id {n : Nat} : rename (n := n) id = id := by
  funext x
  induction x with
  | var i => simp [rename]
  | lam x ih => simp [rename, ih]
  | app x y ih1 ih2 => simp [rename, ih1, ih2]
  | lit x => simp [rename]

@[simp]
theorem rename_comp {f : Fin u → Fin v} {g : Fin v → Fin w} : rename (g ∘ f) = rename g ∘ rename f := by
  funext x
  simp
  induction x generalizing g v w with
  | var i => simp [rename]
  | lam x ih =>
    simp [rename]
    exact ih (f := Rename.lift f) (g := Rename.lift g)
  | app x y ih1 ih2 => simp [rename, ih1, ih2]
  | lit x => simp [rename]

@[simp]
theorem subst_var : subst σ (Term.var i) = σ i := by
  simp [subst]

@[simp]
theorem subst_by_var {n : Nat} : subst (n := n) Term.var = id := by
  funext x
  induction x with
  | var i => simp [subst]
  | lam x ih => simp [subst, ih]
  | app x y ih1 ih2 => simp [subst, ih1, ih2]
  | lit x => simp [subst]

@[simp] lemma Rename.lift_zero (ρ : Fin u → Fin v) :
  Rename.lift ρ 0 = 0 := by
  rfl

@[simp] lemma Rename.lift_succ (ρ : Fin u → Fin v) (i : Fin u) :
  Rename.lift ρ (Fin.succ i) = Fin.succ (ρ i) := by
  rfl

theorem rename_rename (ρ₁ : Fin u → Fin v) (ρ₂ : Fin v → Fin w) (t : Term u) :
  rename ρ₂ (rename ρ₁ t) = rename (ρ₂ ∘ ρ₁) t := by
  induction t generalizing v w with
  | var i => simp
  | lam t ih => simp
  | app t s iht ihs => simp
  | lit n => simp

lemma rename_lift_succ (ρ : Fin w → Fin v) (t : Term w) :
  rename (Rename.lift ρ) (rename Fin.succ t)
    = rename Fin.succ (rename ρ t) := by
  calc
    rename (Rename.lift ρ) (rename Fin.succ t)
      = rename ((Rename.lift ρ) ∘ Fin.succ) t := by rw [rename_rename]
    _ = rename (Fin.succ ∘ ρ) t := by rfl
    _ = rename Fin.succ (rename ρ t) := by rw [rename_rename]

lemma rename_subst (ρ : Fin v → Fin w) (σ : Fin u → Term v) (t : Term u) : rename ρ (subst σ t) = subst (fun x => rename ρ (σ x)) t := by
  induction t generalizing v w with
  | var i => simp
  | lam x ih =>
    simp [subst, rename]
    rw [ih (Rename.lift ρ) (Subst.lift σ)]
    congr 1
    funext i
    simp [Subst.lift]
    split
    . simp [rename, Rename.lift]
    . rename_i h'
      rw [rename_lift_succ]
  | app x y ih1 ih2 => simp [subst, rename, ih1, ih2]
  | lit x => simp [subst, rename]

lemma subst_rename (σ : Fin v → Term w) (ρ : Fin u → Fin v) (t : Term u) :
  subst σ (rename ρ t) = subst (fun x => σ (ρ x)) t := by
  induction t generalizing v w with
  | var i => simp [rename]
  | lam x ih =>
    simp [subst, rename]
    rw [ih (Subst.lift σ) (Rename.lift ρ)]
    congr 1
    funext y
    simp [Rename.lift]
    split
    . rename_i h1
      simp [h1]
    . rename_i h1
      simp [Subst.lift]
      split
      . rename_i h2
        simp [Fin.succ_ne_zero] at h2
      . rfl
  | app x y ih1 ih2 => simp [subst, rename, ih1, ih2]
  | lit x => simp [subst, rename]

lemma interaction (σ : Fin v → Term w) (ρ : Fin u → Fin v) (t : Term u) :
  subst σ (rename ρ t) = subst (fun x => σ (ρ x)) t := subst_rename σ ρ t

theorem Subst.lift_subst_comp {σ1 : Fin u → Term v} {σ2 : Fin v → Term w} : Subst.lift (subst σ2 ∘ σ1) = subst (Subst.lift σ2) ∘ Subst.lift σ1 := by
  funext i
  simp [Subst.lift]
  split
  . simp
  . rename_i h
    change rename Fin.succ (subst σ2 (σ1 (i.pred h))) = subst (Subst.lift σ2) (rename Fin.succ (σ1 (i.pred h)))
    rw [subst_rename, rename_subst]
    rfl

theorem subst_comp_subst {σ1 : Fin u → Term v} {σ2 : Fin v → Term w}
    : subst σ2 ∘ subst σ1 = subst (subst σ2 ∘ σ1) := by
  funext x
  simp
  induction x generalizing σ2 v w with
  | var i => simp [subst]
  | lam x ih =>
    simp [subst]
    simp [ih]
    rw [Subst.lift_subst_comp]
  | app x y ih1 ih2 => simp [subst, ih1, ih2]
  | lit x => simp [subst]

def unbind (x : Term n) : Fin (n + 1) → Term n := fun i =>
  if h : i = 0 then
    x
  else
    .var (i.pred h)

-- parallel
inductive Par : {n : Nat} → Term n → Term n → Prop where
  | var (i) :
      Par (.var i) (.var i)
  | app {x x' y y'} :
      Par x x' → Par y y' →
      Par (.app x y) (.app x' y')
  | lam {body body'} :
      Par body body' →
      Par (.lam body) (.lam body')
  | beta {body body' x x'} :
      Par body body' → Par x x' →
      Par (.app (.lam body) x) (subst (unbind x') body')
  | lit (x) : Par (Term.lit x) (Term.lit x)

attribute [simp] Par.var Par.lit

infix:200 " ⇒ " => Par

@[simp, refl]
theorem Par.refl : (t : Term n) → t ⇒ t
  | .var i   => by simp
  | .lit x   => by simp
  | .app t u => Par.app (Par.refl t) (Par.refl u)
  | .lam b   => Par.lam (Par.refl b)

lemma rename_subst_unbind
  (ρ : Rename n m) (x : Term n) (body : Term (n + 1)) :
  rename ρ (subst (unbind x) body)
    = subst (unbind (rename ρ x)) (rename ρ.lift body) := by
  rw [rename_subst, subst_rename]
  congr 1
  funext i
  unfold unbind
  split
  . rename_i h
    simp
    intro hn
    exfalso
    apply hn
    rw [h]
    simp [Rename.lift]
  . rename_i h
    split
    . rename_i hn
      simp [Rename.lift] at hn
      specialize hn h
      simp [Fin.succ_ne_zero] at hn
    . rename_i hn
      simp [rename]
      simp [Rename.lift]
      split
      . contradiction
      . rfl

theorem Par.congr_rename {σ : Rename n m} : a ⇒ b → rename σ a ⇒ rename σ b := by
  intro h
  induction h generalizing m with
  | var i => simp [rename]
  | @app x x' y y' z h2 h3 ih1 ih2 =>
    simp [rename]
    apply Par.app
    . simp [ih1]
    . simp [ih2]
  | @lam n' body body' h1 ih1 =>
    simp [rename]
    apply Par.lam
    apply ih1
  | @beta n' a' b' c' d' h5 h6 ih1 ih2 =>
    simp [rename]
    have hb : rename σ.lift a' ⇒ rename σ.lift b' := ih1 (σ := σ.lift)
    have hx : rename σ c' ⇒ rename σ d' := ih2 (σ := σ)
    rw [rename_subst_unbind]
    apply Par.beta hb hx
  | lit l => simp [rename]

lemma subst_subst : subst σ₂ (subst σ₁ t) = subst (fun i => subst σ₂ (σ₁ i)) t := by
  change (subst σ₂ ∘ (subst σ₁)) t = subst (fun i ↦ subst σ₂ (σ₁ i)) t
  rw [subst_comp_subst]
  congr

lemma rename_succ_ne_var_zero : rename Fin.succ x ≠ Term.var 0 := by
  intro hn
  cases x <;> simp [rename] at hn
  simp [Fin.succ_ne_zero] at hn

lemma Subst.lift_ne_zero {i : Fin (n + 1)} : (h : i ≠ 0) → Subst.lift σ i = rename Fin.succ (σ (i.pred h)) := by
  intro h
  simp [Subst.lift]
  rw [dif_neg h]

lemma subst_beta_fusion
  (σ' : Fin n' → Term m) (d' : Term n') (b' : Term (n' + 1)) :
  subst σ' (subst (unbind d') b')
    = subst (unbind (subst σ' d')) (subst (Subst.lift σ') b') := by
  cases b' with
  | var i =>
    simp [unbind]
    split
    . rename_i h
      rw [h]
      simp [unbind]
    . rename_i h
      rw [Subst.lift_ne_zero h]
      rw [subst_rename]
      simp [subst]
      simp [unbind]
      simp [Fin.succ_ne_zero]
  | app x y =>
    simp [subst]
    refine ⟨?_, ?_⟩
    . apply subst_beta_fusion
    . apply subst_beta_fusion
  | lam body =>
    simp [subst_subst]
    congr 1
    ext i
    simp [unbind]
    split
    . rename_i h
      rw [h]
      simp [unbind]
    . rename_i h
      rw [Subst.lift_ne_zero h]
      rw [subst_rename]
      simp [subst]
      simp [unbind]
      simp [Fin.succ_ne_zero]
  | lit l => simp [subst]

theorem Par.stable {t t' : Term n} {σ σ' : Fin n → Term m}
  (h  : t ⇒ t')
  (hs : ∀ i, (σ i) ⇒ (σ' i)) :
    (subst σ t) ⇒ (subst σ' t') := by
  induction h generalizing m with
  | var i =>
    simp [subst]
    simp [hs]
  | @app n' x x' y y' h3 h4 ih1 ih2 =>
    simp [subst]
    apply Par.app
    . apply ih1 hs
    . apply ih2 hs
  | @lam n' body body' h1 ih1 =>
    simp [subst]
    apply Par.lam
    have := ih1 (σ := Subst.lift σ) (σ' := Subst.lift σ')
    apply this
    intro i
    simp [Subst.lift]
    split
    . simp
    . apply Par.congr_rename
      apply hs
  | @beta n' a' b' c' d' h5 h6 ih1 ih2 =>
    simp [subst]
    have hsLift : ∀ i : Fin (n' + 1), (Subst.lift σ i) ⇒ (Subst.lift σ' i) := by
      intro i
      simp [Subst.lift]
      split
      . simp
      . apply Par.congr_rename
        apply hs
    have hBody : subst (Subst.lift σ) a' ⇒ subst (Subst.lift σ') b' :=
      ih1 (σ := Subst.lift σ) (σ' := Subst.lift σ') hsLift
    have hArg : subst σ c' ⇒ subst σ' d' :=
      ih2 (σ := σ) (σ' := σ') hs
    rw [subst_beta_fusion]
    apply Par.beta hBody hArg
  | lit l => simp [subst]

theorem Par.confluence {t u v : Term n} : t ⇒ u → t ⇒ v → ∃ w, u ⇒ w ∧ v ⇒ w := by
  intro h1 h2
  induction h1 with
  | var i =>
    exists .var i
    cases h2
    simp
  | @app n' x x' y y' h3 h4 ih1 ih2 =>
    cases h2 with
    | @app m _ a' _ b' h5 h6 =>
      have ⟨o, h7⟩ := ih1 h5
      have ⟨o', h8⟩ := ih2 h6
      use (Term.app o o')
      refine ⟨Par.app h7.1 h8.1, Par.app h7.2 h8.2⟩
    | @beta _ a b _ c h5 h6 =>
      have : a.lam ⇒ b.lam := by
        apply Par.lam h5
      have ⟨o, h7⟩ := ih1 this
      have ⟨o', h8⟩ := ih2 h6
      cases o <;> cases h7.2
      rename_i b' h9
      cases x' <;> cases h3
      rename_i x'' h10
      let s := subst (unbind o') b'
      use s
      refine ⟨?_, ?_⟩
      . simp [s]
        apply Par.beta
        . cases h7.1; assumption
        . exact h8.1
      . simp [s]
        apply Par.stable
        . apply h9
        . intro i
          simp [unbind]
          split
          . exact h8.2
          . simp
  | @lam n' body body' h1 ih1 =>
    cases h2
    rename_i body'' h2
    have ⟨o, h3⟩ := ih1 h2
    use o.lam
    refine ⟨?_, ?_⟩
    . apply Par.lam h3.1
    . apply Par.lam h3.2
  | @beta n' a' b' c' d' h5 h6 ih1 ih2 =>
    cases h2 with
    | @app m _ x _ y h7 h8 =>
      cases x <;> cases h7
      rename_i a'' h9
      have ⟨o, h10⟩ := ih1 h9
      have ⟨o', h11⟩ := ih2 h8
      let s := subst (unbind o') o
      use s
      simp [s]
      refine ⟨?_, ?_⟩
      . apply Par.stable
        . exact h10.1
        . intro i
          simp [unbind]
          split
          . exact h11.1
          . simp
      . apply Par.beta
        . exact h10.2
        . exact h11.2
    | @beta n'' a'' b'' c'' d'' h7 h8 =>
      have ⟨o, h9⟩ := ih1 h7
      have ⟨o', h10⟩ := ih2 h8
      use subst (unbind o') o
      refine ⟨?_, ?_⟩
      . apply Par.stable h9.1
        intro i
        simp [unbind]
        split
        . exact h10.1
        . simp
      . apply Par.stable h9.2
        intro i
        simp [unbind]
        split
        . exact h10.2
        . simp
  | lit l =>
    cases h2
    use Term.lit l

def Term.beta_para : Term n → Term n
  | x@(.var _) => x
  | .lam body => .lam body.beta_para
  | .app (.lam body) x =>
    subst (unbind x.beta_para) body.beta_para
  | .app x y => .app x.beta_para y.beta_para
  | x@(.lit _) => x

theorem Term.para_beta_sound (x : Term n) : x ⇒ x.beta_para := by
  induction x with
  | var i => simp [Term.beta_para]
  | lit l => simp [Term.beta_para]
  | app x y ih1 ih2 =>
    cases x with
    | var j =>
      simp [Term.beta_para]
      apply Par.app (by simp) ih2
    | lit l =>
      simp [Term.beta_para]
      apply Par.app (by simp) ih2
    | app a b =>
      simp [Term.beta_para]
      apply Par.app ih1 ih2
    | lam body =>
      simp [Term.beta_para]
      apply Par.beta ?_ ih2
      cases ih1
      assumption
  | lam body ih =>
    simp [Term.beta_para]
    apply Par.lam
    exact ih

inductive Beta : {n : Nat} → Term n → Term n → Prop where
  | beta {n} {body : Term (n + 1)} {x : Term n} :
      Beta (.app (.lam body) x) (subst (unbind x) body)
  | appL {n} {t t' u : Term n} :
      Beta t t' → Beta (.app t u) (.app t' u)
  | appR {n} {t u u' : Term n} :
      Beta u u' → Beta (.app t u) (.app t u')
  | lam {n} {b b' : Term (n + 1)} :
      Beta b b' → Beta (.lam b) (.lam b')

infix:200 " →β "  => Beta

abbrev BetaStar (t u : Term n) : Prop := Relation.ReflTransGen (Beta (n := n)) t u

infix:200 " →β* " => BetaStar

theorem Beta.par {a b : Term n} : a →β b → a ⇒ b := by
  intro h
  induction h with
  | @beta m body x =>
    apply Par.beta
    simp
    simp
  | @appL m x x' y h1 ih =>
    apply Par.app ih
    simp
  | @appR m x y y' h1 ih =>
    apply Par.app ?_ ih
    simp
  | @lam m x x' h ih =>
    apply Par.lam ih

theorem BetaStar.single : x →β y → x →β* y := by
  intro h
  apply Relation.ReflTransGen.single h

theorem BetaStar.transL (y : Term n) : x →β* y → y →β z → x →β* z := by
  intro h1 h2
  apply Relation.ReflTransGen.tail
  . apply h1
  . exact h2

theorem BetaStar.transR (y : Term n) : x →β y → y →β* z → x →β* z := by
  intro h1 h2
  trans y
  . apply Relation.ReflTransGen.single h1
  . apply h2

theorem BetaStar.appL {x x' y : Term n} : x →β* x' → x.app y →β* x'.app y := by
  intro h
  induction h generalizing y
  . rfl
  . expose_names
    apply Relation.ReflTransGen.tail
    . apply a_ih
    . apply Beta.appL h_1

theorem BetaStar.appR {x y y' : Term n} : y →β* y' → x.app y →β* x.app y' := by
  intro h
  induction h generalizing x
  . rfl
  . expose_names
    apply Relation.ReflTransGen.tail
    . apply a_ih
    . apply Beta.appR h_1

theorem BetaStar.lam {x x' : Term (n + 1)} : x →β* x' → x.lam →β* x'.lam := by
  intro h
  induction h
  . rfl
  . expose_names
    apply Relation.ReflTransGen.tail
    . apply a_ih
    . apply Beta.lam h_1

theorem BetaStar.beta {body : Term (n + 1)} {x : Term n} : (Term.app (.lam body) x) →β* (subst (unbind x) body) := by
  apply Relation.ReflTransGen.single
  apply Beta.beta

theorem Par.serialize {a b : Term n} : a ⇒ b → a →β* b := by
  intro h
  induction h with
  | var i => rfl
  | lit l => rfl
  | @app m x x' y y' h5 h6 ih1 ih2 =>
    trans
    . apply BetaStar.appL ih1
    . apply BetaStar.appR ih2
  | @lam n' body body' h1 ih1 =>
    apply BetaStar.lam ih1
  | @beta n' a' b' c' d' h7 h8 ih1 ih2 =>
    trans (b'.lam.app c')
    . apply BetaStar.appL
      apply BetaStar.lam ih1
    . trans (b'.lam.app d')
      . apply BetaStar.appR ih2
      . apply BetaStar.beta

abbrev ParStar (t u : Term n) : Prop := Relation.TransGen (Par (n := n)) t u

infix:200 " ⇒* "  => ParStar

theorem ParStar.single : x ⇒ y → x ⇒* y := by
  intro h
  apply Relation.TransGen.single h

@[refl]
theorem ParStar.refl : x ⇒* x := by
  apply Relation.TransGen.single
  rfl

theorem ParStar.inclusion_beta_star : x ⇒* y → x →β* y := by
  intro h
  induction h with
  | @single a h =>
    apply h.serialize
  | @tail a b c h ih =>
    trans a
    . apply ih
    . apply h.serialize

theorem BetaStar.inclusion_par_star : x →β* y → x ⇒* y := by
  intro h
  induction h with
  | refl => apply ParStar.refl
  | @tail a b h1 h2 ih =>
    trans a
    . apply ih
    . apply Relation.TransGen.single
      apply h2.par

theorem ParStar.eqv_beta_star : x ⇒* y ↔ x →β* y := ⟨ParStar.inclusion_beta_star, BetaStar.inclusion_par_star⟩

lemma Par.strip {t u v : Term n} (htu : t ⇒ u) (htv : t ⇒* v) :
    ∃ w, u ⇒* w ∧ v ⇒* w := by
  induction htv using Relation.TransGen.head_induction_on generalizing u with
  | @single a h1 =>
    have ⟨w, h3⟩ := Par.confluence h1 htu
    use w
    refine ⟨?_, ?_⟩
    . apply ParStar.single h3.2
    . apply ParStar.single h3.1
  | @head b c h2 h3 h4 =>
    have ⟨o, h5, h6⟩ := Par.confluence h2 htu
    have ⟨w, h7, h8⟩ := h4 h5
    use w
    refine ⟨?_, ?_⟩
    . apply Relation.TransGen.head h6 h7
    . exact h8

theorem ParStar.confluence {t u v : Term n} (htu : t ⇒* u) (htv : t ⇒* v) :
    ∃ w, u ⇒* w ∧ v ⇒* w := by
  induction htu using Relation.TransGen.head_induction_on generalizing v with
  | @single a h1 =>
    have ⟨w, h3⟩ := Par.strip h1 htv
    use w
  | @head b c h2 h3 h4 =>
    have ⟨o, h5, h6⟩ := Par.strip h2 htv
    have ⟨w, h7, h8⟩ := h4 h5
    use w
    simp [h7]
    apply Relation.TransGen.trans h6 h8

theorem BetaStar.confluence {t u v : Term n} (htu : t →β* u) (htv : t →β* v) :
    ∃ w, u →β* w ∧ v →β* w := by
  rw [← ParStar.eqv_beta_star] at htu htv
  have ⟨w, h⟩ := ParStar.confluence htu htv
  use w
  rw [ParStar.eqv_beta_star] at h
  rw [ParStar.eqv_beta_star] at h
  simp [h]
