-- in this file we characterize the ways in which the n=2 case could fail

import Polymorphisms.Basic
import Polymorphisms.Restrict
import Polymorphisms.Classify
import Polymorphisms.Bijection
open Finset
open Classical

variable {pred : Predicate} {Φ : Set (format pred)} {poly : Polymorphism pred 2}

-- definitions

def set_coord_to {m : ℕ} {a : range m → ℕ} (i₀ : range m) (σ : range (a i₀))
  (y : (i : range m) → range (a i)) (i : range m) : range (a i) :=
  if h : i = i₀ then ⟨σ, by simp [h]⟩ else (y i)

def is_closed_under (pred : Predicate) (i : range pred.m) (σ : range (pred.a i)) :=
  ∀ y, pred.P y → pred.P (set_coord_to i σ y)

def has_closure (pred : Predicate) :=
  ∃ i σ, is_closed_under pred i σ

def AND₂ (a : ℕ) [AtLeast2 a] (x : range 2 → range a) : range a :=
  if x range_0 = range_1 ∧ x range_1 = range_1 then range_1 else range_0

def OR₂ (a : ℕ) [AtLeast2 a] (x : range 2 → range a) : range a :=
  if x range_0 = range_0 ∧ x range_1 = range_0 then range_0 else range_1

def is_AND_OR_poly (poly : Polymorphism pred 2) :=
  (∀ i, (h : pred.a i = 2) → poly.fs i = AND₂ (pred.a i) ∨ poly.fs i = OR₂ (pred.a i)) ∧
  (∀ i, pred.a i > 2 → poly.fs i = fun x => x range_0)

def has_AND_OR_poly (pred : Predicate) :=
  (∃ i, pred.a i = 2) ∧
  ∃ poly : Polymorphism pred 2, is_AND_OR_poly poly

def is_Latin_square {a : ℕ} (f : (range 2 → range a) → range a) :=
  (∀ σ : range a, (fun τ => f (cons_input σ τ)).Bijective) ∧
  (∀ σ : range a, (fun τ => f (cons_input τ σ)).Bijective)

def is_Latin_square_poly (Φ : Set (format pred)) (poly : Polymorphism pred 2) :=
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input (y i) τ)) ∈ Φ) ∧
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ)

def has_Latin_square_poly (pred : Predicate) (Φ : Set (format pred)) :=
  ∃ poly : Polymorphism pred 2, is_Latin_square_poly Φ poly

-- proofs
namespace ReductionTo1

-- definition and properties of h

def h_func (poly : Polymorphism pred 2) (i : range pred.m) (σ : range (pred.a i)) :
  Option (range (pred.a i)) :=
  match φ_classify (fun τ => poly.fs i (cons_input τ σ)) with
  | .const τ => some τ
  | .nonconst _ _ => none

lemma h_func_const (poly : Polymorphism pred 2) (i : range pred.m) (σ ρ : range (pred.a i)) :
  h_func poly i σ = some ρ ↔ ∀ τ, poly.fs i (cons_input τ σ) = ρ := by
  constructor
  · intro h
    unfold h_func at h
    split at h
    case h_1 τ h' =>
        simp at h
        rw [←h]
        exact (φ_const_spec _ _).mp h'
    case h_2 => contradiction
  · intro h
    unfold h_func
    split
    case h_1 τ h' =>
      congr
      replace h' := (φ_const_spec _ _).mp h'
      rw [←h range_0, h' range_0]
    case h_2 h' =>
      have := (φ_const_spec _ _).mpr h
      rw [h'] at this
      contradiction

def h_all_none (poly : Polymorphism pred 2) (y : (i : range pred.m) → range (pred.a i)) :=
  ∀ i, h_func poly i (y i) = none

def dictatorial_of_h_all_none (htrivial : trivial_for₁ pred Φ)
  {poly y} (Py : pred.P y) (h : h_all_none poly y) :
  (restrict_polymorphism₁ poly Py).fs ∈ Φ := by
  cases htrivial (restrict_polymorphism₁ poly Py)
  case inl h => exact h
  case inr h =>
    obtain ⟨c, hc⟩ := h
    have cdom_empty : ∀ i : range pred.m, i ∉ c.dom := by
      intro i
      by_contra hi
      let i' : c.dom := ⟨i, hi⟩
      have hsome : h_func poly i (y i) = some (c.ρ i') := by
        apply (h_func_const _ _ _ _).mpr
        intro τ
        have := hc i'
        simp [restrict_polymorphism₁] at this
        apply congr_fun this
      have hnone := h i
      rw [hsome] at hnone
      contradiction
    obtain ⟨x, y, hx, hy, hxy⟩ := pred.dep range_0
    have : pred.P y := by
      apply c.cert
      intro i
      by_contra
      apply cdom_empty i
      exact Subtype.coe_prop i
    contradiction

def certificate_of_not_h_all_none (htrivial : trivial_for₁ pred Φ) (hperm : permutational Φ)
  {poly y} (Py : pred.P y) (h : ¬ h_all_none poly y) :
  ∃ c : Certificate pred, ∀ i : c.dom, h_func poly i (y i) = c.ρ i := by
  cases htrivial (restrict_polymorphism₁ poly Py)
  case inr hcert =>
    obtain ⟨c, hc⟩ := hcert
    use c
    intro i
    apply (h_func_const _ _ _ _).mpr
    intro τ
    have := hc i
    simp [restrict_polymorphism₁] at this
    apply congr_fun this
  case inl hdict =>
    by_contra
    unfold h_all_none at h
    push_neg at h
    obtain ⟨i, hnotnone⟩ := h
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp hnotnone
    replace hτ := (h_func_const _ _ _ _).mp hτ
    unfold is_dictatorship₁ at hdict
    replace hperm := hperm _ hdict i
    simp only [restrict_polymorphism₁] at hperm
    replace hperm := hperm.1
    have := hperm (Eq.trans (hτ range_0) (Eq.symm (hτ range_1)))
    simp [range_0, range_1] at this

-- case 1: the certificate case holds for all y

noncomputable def g_func (poly : Polymorphism pred 2) (i : range pred.m) (σ : range (pred.a i)) :
  range (pred.a i) :=
  match h_func poly i σ with
  | some τ => τ
  | none =>
    if h : ∃ σ', (h_func poly i σ').isSome then
      if h_func poly i (choose h) = some range_0 then range_1 else range_0
    else
      σ

lemma g_of_h_some {poly : Polymorphism pred 2} {i : range pred.m}
  {σ τ : range (pred.a i)} (h : h_func poly i σ = some τ) :
  g_func poly i σ = τ := by
  simp [g_func, h]

lemma g_func_const {poly : Polymorphism pred 2} {i : range pred.m} {τ : range (pred.a i)}
  (hconst : ∀ σ, g_func poly i σ = τ) :
  ∀ σ, h_func poly i σ = some τ := by
  by_contra! h
  obtain ⟨σ, hσ⟩ := h
  have gσ := hconst σ
  cases hh : h_func poly i σ
  case some τ' =>
    apply hσ
    simp [g_func, hh] at gσ
    rw [←gσ]
    exact hh
  case none =>
    by_cases hsome : ∃ σ', (h_func poly i σ').isSome
    case pos =>
      obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (choose_spec hsome)
      have hc := hconst (choose hsome)
      simp [g_func, hh, hτ'] at hc
      rw [hc] at hτ'
      simp [g_func, hh, hsome, hτ'] at gσ
      rw [←hc] at gσ
      by_cases hval : τ' = range_0
      all_goals simp [range_0] at hval
      all_goals simp [hval, range_0, range_1] at gσ
      apply hval
      symm; assumption
    case neg =>
      have hsome' : ∀ σ', h_func poly i σ' = none := by
        push_neg at hsome
        intro σ'
        exact Option.not_isSome_iff_eq_none.mp (hsome σ')
      conv at hconst =>
        ext σ
        simp [g_func, hsome, hsome' σ]
      have h_0 := hconst range_0
      have h_1 := hconst range_1
      rw [←h_0] at h_1
      simp [range_0, range_1] at h_1

lemma g_func_const' {poly : Polymorphism pred 2} {i : range pred.m} {τ : range (pred.a i)}
  (hconst : ∀ σ, g_func poly i σ = τ) :
  ∀ x, poly.fs i x = τ := by
  intro x
  have := g_func_const hconst (x range_1)
  have := (h_func_const poly i (x range_1) τ).mp this
  convert this (x range_0)
  simp

noncomputable def g_polymorphism
  (htrivial : trivial_for₁ pred Φ) (hperm : permutational Φ)
  (poly : Polymorphism pred 2)
  (all_cert : ∀ y, pred.P y → ¬ h_all_none poly y) :
  Polymorphism₁ pred :=
{
  fs := g_func poly,
  app y Py := by
    obtain ⟨c, hc⟩ := certificate_of_not_h_all_none htrivial hperm Py (all_cert y Py)
    apply c.cert
    intro i
    apply g_of_h_some (hc i)
}

def neg₂ {a} [AtLeast2 a] (σ : range a) : range a :=
  if σ = range_0 then range_1 else range_0

lemma neg₂_ne {a} [AtLeast2 a] (σ : range a) : σ ≠ neg₂ σ := by
  simp [neg₂]
  split
  case isTrue h => rw [h]; simp [range_0, range_1]
  case isFalse h => assumption

lemma neg₂_ne' {a} [AtLeast2 a] (σ : range a) : σ.1 ≠ (neg₂ σ).1 := by
  have := neg₂_ne σ
  contrapose! this
  apply Subtype.eq
  assumption

lemma neg₂_0_or_1 {a} [AtLeast2 a] (σ : range a) :
  neg₂ σ = range_0 ∨ neg₂ σ = range_1 := by
  simp [neg₂]
  by_cases σ = range_0
  case pos h =>
    right
    intro h'
    simp [range_0, range_1]
    contradiction
  case neg h =>
    left
    intro h'
    simp [range_0, range_1]
    contradiction

lemma neg₂_0_or_1' {a} [AtLeast2 a] (σ : range a) :
  (neg₂ σ).1 = 0 ∨ (neg₂ σ).1 = 1 := by
  cases neg₂_0_or_1 σ
  case inl h => left; rw [h, range_0]
  case inr h => right; rw [h, range_1]

lemma neg₂_dichotomy {a} [AtLeast2 a] (ha : a = 2) {σ τ : range a} :
  σ ≠ τ ↔ σ = neg₂ τ := by
  constructor
  · intro h
    cases hσ : of_range_2' ha σ <;> cases hτ : of_range_2' ha τ
    all_goals simp [*] at h
    all_goals simp [neg₂, range_0, range_1, *]
  · intro h
    cases hσ : of_range_2' ha σ <;> cases hτ : of_range_2' ha τ
    all_goals simp [neg₂, range_0, range_1, *] at h
    all_goals simp [range_0, range_1, *]

lemma trivial_for_2_of_trivial_for_1_all_cert (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2)
  (all_cert : ∀ y, pred.P y → ¬ h_all_none poly y) :
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ) := by
  let g := g_polymorphism htrivial hperm poly all_cert
  cases htrivial g
  case inr hcert =>
    obtain ⟨c, hc⟩ := hcert
    simp only [g, g_polymorphism] at hc
    right; left
    use c
    intro i
    apply g_func_const'
    intro σ
    exact congrFun (hc i) σ
  case inl hdict =>
    unfold is_dictatorship₁ at hdict
    have g_bijective : ∀ i, (g.fs i).Bijective := by
      apply hperm
      exact hdict
    let inv_g := inverse_poly g g_bijective
    by_cases ∃ i₀ σ₀, h_func poly i₀ σ₀ = none
    case pos h =>
      obtain ⟨i₀, σ₀, hnone⟩ := h
      have hset : ∀ y, pred.P y → y i₀ = σ₀ →
        ∀ τ, pred.P (set_coord_to i₀ τ y) := by
        intro y Py hy τ
        obtain ⟨c, hc⟩ := certificate_of_not_h_all_none htrivial hperm Py (all_cert y Py)
        let μ : Certificate pred :=
        {
          dom := c.dom,
          ρ i := inv_g.fs i (c.ρ i),
          cert x hx := by
            let y i := g.fs i (x i)
            have : ∀ i : c.dom, y i = c.ρ i := by
              intro i
              simp [y]
              rw [hx i]
              simp [inv_g, inverse_poly]
              rw [Function.rightInverse_invFun (g_bijective i).2]
            have := c.cert y this
            convert inv_g.app y this with i
            simp [inv_g, inverse_poly, y]
            rw [Function.leftInverse_invFun (g_bijective i).1]
        }
        have hi₀ : i₀ ∉ μ.dom := by
          contrapose! hnone
          simp [μ] at hnone
          have := hc ⟨i₀, hnone⟩
          simp at this
          rw [hy] at this
          rw [this]
          simp
        apply μ.cert
        intro i
        unfold set_coord_to
        split
        case isTrue h =>
          exfalso; apply hi₀
          rw [←h]
          exact i.coe_prop
        case isFalse h =>
          simp [μ, inv_g, inverse_poly, g, g_polymorphism]
          rw [←g_of_h_some (hc i)]
          symm
          exact Function.leftInverse_invFun (g_bijective i).1 (y i)
      by_cases pred.a i₀ = 2
      case pos hbool =>
        right; right; left
        use i₀
        use neg₂ σ₀
        intro y Py
        by_cases y i₀ = σ₀
        case pos h =>
          exact hset y Py h (neg₂ σ₀)
        case neg h =>
          convert Py
          unfold set_coord_to
          funext i
          split
          case isFalse => rfl
          case isTrue h' =>
            have := (neg₂_dichotomy hbool).mp h
            refine Eq.symm (Subtype.coe_eq_of_eq_mk ?_)
            rw [←this, h']
      case neg hbool =>
        replace hbool : pred.a i₀ ≥ 3 := by
          have := pred.ha i₀
          omega
        let bad : Polymorphism₁ pred :=
        {
          fs i σ :=
            if i = i₀ ∧ σ.1 = σ₀.1 then
              neg₂ σ
            else
              σ,
          app y Py := by
            by_cases y i₀ = σ₀
            case pos h =>
              convert hset y Py h (neg₂ σ₀) with i
              unfold set_coord_to
              split
              case isTrue h' =>
                subst h h'
                simp
              case isFalse h' =>
                simp [h']
            case neg h =>
              convert Py with i
              simp
              intro hi
              subst hi
              intro hyi
              replace hyi := Subtype.coe_eq_of_eq_mk hyi
              rw [hyi] at h
              exfalso
              apply h
              apply Subtype.coe_eq_of_eq_mk
              simp
        }
        cases htrivial bad
        case inl hdict =>
          exfalso
          unfold is_dictatorship₁ at hdict
          have injective := (hperm _ hdict i₀).1
          have : bad.fs i₀ σ₀ = bad.fs i₀ (neg₂ σ₀) := by
            simp [bad]
            split
            case isTrue h =>
              exfalso
              apply neg₂_ne σ₀
              symm
              apply Subtype.coe_eq_of_eq_mk h
            case isFalse h => rfl
          have error := injective this
          apply neg₂_ne σ₀
          assumption
        case inr hcert =>
          exfalso
          obtain ⟨c, hc⟩ := hcert
          obtain ⟨i, hi⟩ := dom_nonempty c
          replace hc := congrFun (hc ⟨i, hi⟩)
          by_cases i = i₀
          case neg h =>
            have h₀ := hc range_0
            have h₁ := hc range_1
            rw [←h₀] at h₁
            simp [bad, h, range_0, range_1] at h₁
          case pos h =>
            have ge3 : pred.a i ≥ 3 := by
              convert hbool
            let neg₀ : range (pred.a i) := ⟨neg₂ σ₀, ?_⟩
            case refine_1 =>
              apply mem_range.mpr
              cases neg₂_0_or_1' σ₀
              case inl h => rw [h]; linarith [ge3]
              case inr h => rw [h]; linarith [ge3]
            have neg₀_ne : neg₀.1 ≠ σ₀.1 := by
              have := neg₂_ne σ₀
              contrapose! this
              simp [neg₀] at this
              symm
              apply Subtype.coe_eq_of_eq_mk this
            let range_2 : range (pred.a i) := ⟨2, ?_⟩
            case refine_1 =>
              apply mem_range.mpr
              linarith [ge3]
            have hn := hc neg₀
            simp [bad, h, neg₀_ne] at hn
            have heq : ∀ σ : range (pred.a i), σ.1 = σ₀.1 ∨ σ.1 = neg₀.1 := by
              intro σ
              by_contra h'
              push_neg at h'
              have := hc σ
              rw [←hn] at this
              simp [bad, h, h'] at this
              apply h'.2
              rw [this]
            have h₂ : σ₀.1 = 2 := by
              cases heq range_2
              case inl h => symm; assumption
              case inr h =>
                cases neg₂_0_or_1' σ₀
                case inl h' =>
                  simp [range_2, neg₀] at h
                  rw [←h] at h'
                  contradiction
                case inr h' =>
                  simp [range_2, neg₀] at h
                  rw [←h] at h'
                  contradiction
            have h₀ : neg₀.1 = 0 := by
              cases heq range_0
              case inl h => rw [h₂] at h; simp [range_0] at h
              case inr h => simp [range_0] at h; symm; assumption
            have h₁ : neg₀.1 = 1 := by
              cases heq range_1
              case inl h => rw [h₂] at h; simp [range_1] at h
              case inr h => simp [range_1] at h; symm; assumption
            rw [h₀] at h₁
            contradiction
    case neg h =>
      push_neg at h
      left
      use range_1, g.fs, hdict
      intro i x
      obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp (h i (x range_1))
      calc
        poly.fs i x = τ := by
          convert (h_func_const poly i (x range_1) τ).mp hτ (x range_0)
          simp
        _ = g.fs i (x range_1) := by
          symm
          exact g_of_h_some hτ

-- case 2: the dictatorial case holds for some y, and h is not all *

noncomputable def G_func (poly : Polymorphism pred 2)
  (z : (i : range pred.m) → range (pred.a i))
  (i : range pred.m) (σ : range (pred.a i)) :
  range (pred.a i) :=
  match h_func poly i σ with
  | some τ => τ
  | none => z i

lemma G_of_h_some {poly : Polymorphism pred 2} {z} {i : range pred.m}
  {σ τ : range (pred.a i)} (h : h_func poly i σ = some τ) :
  G_func poly z i σ = τ := by
  simp [G_func, h]

noncomputable def G_polymorphism
  (htrivial : trivial_for₁ pred Φ) (hperm : permutational Φ)
  (poly : Polymorphism pred 2) {z} (Pz : pred.P z) :
  Polymorphism₁ pred :=
{
  fs := G_func poly z,
  app y Py := by
    by_cases h_all_none poly y
    case pos htrue =>
      unfold G_func
      conv =>
        congr
        ext i
        simp [htrue i]
      exact Pz
    case neg hfalse =>
      obtain ⟨c, hc⟩ := certificate_of_not_h_all_none htrivial hperm Py hfalse
      apply c.cert
      intro i
      apply G_of_h_some (hc i)
}

-- must be in mathlib4...
lemma fun_diff {t₁ : Type} {t₂ : t₁ → Type} {f g : (i : t₁) → t₂ i} (h : f ≠ g) :
  ∃ x, f x ≠ g x := by
    contrapose! h
    funext x
    apply h

lemma perm_hole {t : Type} {f g : t → t} {x : t}
  (hf : f.Bijective) (hg : g.Bijective)
  (hx : ∀ y ≠ x, f y = g y) : f x = g x := by
  obtain ⟨z, hz⟩ := hg.2 (f x)
  by_cases z = x
  case pos h =>
    rw [h] at hz
    symm
    exact hz
  case neg h =>
    push_neg at h
    have := hx z h
    have := Eq.trans this hz
    have := hf.1 this
    contradiction

lemma exists_3 {a} (ha : a ≥ 3) (γ : range a) :
  ∃ α β, α ≠ β ∧ α ≠ γ ∧ β ≠ γ := by
  let r0 : range a := ⟨0, by apply mem_range.mpr; omega⟩
  let r1 : range a := ⟨1, by apply mem_range.mpr; omega⟩
  let r2 : range a := ⟨2, by apply mem_range.mpr; omega⟩
  match hγ : γ.1 with
  | 0 =>
    use r1, r2
    constructor <;> try constructor
    simp [r1, r2]
    simp [r1]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp
    simp [r2]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp
  | 1 =>
    use r0, r2
    constructor <;> try constructor
    simp [r0, r2]
    simp [r0]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp
    simp [r2]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp
  | n+2 =>
    use r0, r1
    constructor <;> try constructor
    simp [r0, r1]
    simp [r0]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp
    simp [r1]; contrapose! hγ; rw [←Subtype.eq_iff.mp hγ]; simp

lemma php3 {a} (ha : a ≥ 3)
  {t : Type} {f : range a → t}
  {α β} (h : ∀ σ : range a, f σ = α ∨ f σ = β) :
  ∃ σ₁ σ₂, σ₁ ≠ σ₂ ∧ f σ₁ = f σ₂ := by
  let r0 : range a := ⟨0, by apply mem_range.mpr; omega⟩
  let r1 : range a := ⟨1, by apply mem_range.mpr; omega⟩
  let r2 : range a := ⟨2, by apply mem_range.mpr; omega⟩
  cases h0 : h r0 <;> cases h1 : h r1 <;> cases h2 : h r2
  case _ => use r0, r1; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r0, r1; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r0, r2; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r1, r2; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r1, r2; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r0, r2; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r0, r1; constructor; simp [r0, r1, r2]; simp [*]
  case _ => use r0, r1; constructor; simp [r0, r1, r2]; simp [*]

lemma trivial_for_2_of_trivial_for_1_exists_dict_dict (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2)
  {η} (Pη : pred.P η) (hη : h_all_none poly η)
  (hdictη : is_dictatorship₁ (G_polymorphism htrivial hperm poly Pη) Φ):
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ) := by
  let Gη := G_polymorphism htrivial hperm poly Pη
  have Gηperm i := hperm Gη.fs hdictη i
  have hnotnone {i σ} (hσ : σ ≠ η i) : (h_func poly i σ).isSome := by
    by_contra h
    replace h := Option.not_isSome_iff_eq_none.mp h
    have Gη_σ : Gη.fs i σ = η i := by
      simp [Gη, G_polymorphism, G_func, h]
    have Gη_η : Gη.fs i (η i) = η i := by
      simp [Gη, G_polymorphism, G_func, hη i]
    apply hσ
    apply (Gηperm i).1
    rw [Gη_σ, Gη_η]
  let B := {i | pred.a i = 2}
  have hP' : ∀ ζ ≠ η, pred.P ζ → (∃ i, i ∈ B) ∧
    ∀ w, (∀ i ∈ B, ζ i = neg₂ (η i) → w i = ζ i) → pred.P w := by
    intro ζ hζ Pζ
    let Gζ := G_polymorphism htrivial hperm poly Pζ
    have Gagree {i σ} (hσ : σ ≠ η i) : Gη.fs i σ = Gζ.fs i σ := by
      simp [Gη, Gζ, G_polymorphism, G_func]
      split
      · rfl
      case _ hnone =>
      have := hnotnone hσ
      rw [hnone] at this
      contradiction
    have Gηhole i : Gη.fs i (η i) = η i := by
      simp [Gη, G_polymorphism, G_func, hη i]
    have Gζhole i : Gζ.fs i (η i) = ζ i := by
      simp [Gζ, G_polymorphism, G_func, hη i]
    cases htrivial Gζ
    case inl hdictζ =>
      obtain ⟨i, hi⟩ := fun_diff hζ
      replace Gηperm := Gηperm i
      have Gζperm := hperm Gζ.fs hdictζ i
      have Gdiff : Gη.fs i (η i) ≠ Gζ.fs i (η i) := by
        simp [Gη, Gζ, G_polymorphism, G_func, hη i]
        push_neg; symm; exact hi
      exfalso
      apply Gdiff
      apply perm_hole <;> try assumption
      intro y hy
      apply Gagree
      assumption
    case inr hcertζ =>
      obtain ⟨c, hc⟩ := hcertζ
      have hB (i : c.dom) : ↑i ∈ B := by
        by_contra! h
        simp [B] at h
        have ha : pred.a i ≥ 3 := by
          have := pred.ha i
          omega
        obtain ⟨α, β, hαβ, hα, hβ⟩ := exists_3 ha (η i)
        have Gα := Eq.trans (Gagree hα) (congrFun (hc i) α)
        have Gβ := Eq.trans (Gagree hβ) (congrFun (hc i) β)
        apply hαβ
        apply (Gηperm i).1
        rw [Gα, Gβ]
      constructor
      · obtain ⟨i', hi'⟩ := dom_nonempty c
        let i : c.dom := ⟨i', hi'⟩
        use i
        apply hB
      intro w hw
      apply c.cert
      intro i
      replace hc := congrFun (hc i)
      replace Gηperm := Gηperm i
      have i_in_B : ↑i ∈ B := by
        by_contra! h
        simp [B] at h
        have ha : pred.a i ≥ 3 := by
          have := pred.ha i
          omega
        obtain ⟨α, β, hαβ, hα, hβ⟩ := exists_3 ha (η i)
        have Gα := Eq.trans (Gagree hα) (hc α)
        have Gβ := Eq.trans (Gagree hβ) (hc β)
        apply hαβ
        apply Gηperm.1
        rw [Gα, Gβ]
      have ζ_neg_η : ζ i = neg₂ (η i) := by
        apply (neg₂_dichotomy i_in_B).mp
        by_contra!
        have Gagree' σ : Gη.fs i σ = Gζ.fs i σ := by
          by_cases σ = η i
          case pos h =>
            rw [h, Gηhole i, Gζhole i]
            symm; assumption
          case neg h =>
            apply Gagree h
        have : Gζ.fs i range_0 = Gζ.fs i range_1 := by
          rw [hc range_0, hc range_1]
        rw [←Gagree' range_0, ←Gagree' range_1] at this
        have := Gηperm.1 this
        simp [range_0, range_1] at this
      have ρ_ζ : c.ρ i = ζ i := by
        rw [←Gζhole i, hc (η i)]
      symm
      rwa [hw i i_in_B ζ_neg_η]
  have hP : ∀ ζ ≠ η, pred.P ζ → ∀ w, (∀ i ∈ B, ζ i = neg₂ (η i) → w i = ζ i) → pred.P w := by
    intro ζ hζ Pζ
    exact (hP' ζ hζ Pζ).2
  have hB : ∀ ζ ≠ η, pred.P ζ → ∃ i, i ∈ B := by
    intro ζ hζ Pζ
    exact (hP' ζ hζ Pζ).1
  let e : Polymorphism pred 2 :=
  {
    fs i x :=
    if i ∈ B then
      if x range_0 = η i ∧ x range_1 = η i then
        η i
      else
        neg₂ (η i)
    else
      (x range_0)
    app xs sat := by
      by_cases (xs · range_0) = η
      case pos hy =>
        replace hy := congrFun hy
        by_cases (xs · range_1) = η
        case pos hz =>
          replace hz := congrFun hz
          convert Pη with i
          by_cases i ∈ B
          case pos hi =>
            simp [hi, hy i, hz i]
          case neg hi =>
            simp [hi, hy i]
        case neg hz =>
          apply hP (xs · range_1)
          · exact hz
          · apply sat
          intro i hi hzi
          have hi' : pred.a i = 2 := by
            simp [B] at hi
            exact hi
          have hzi' := (neg₂_dichotomy hi').mpr hzi
          simp [hi, hzi']
          symm; exact hzi
      case neg hy =>
        apply hP (xs · range_0)
        · exact hy
        · apply sat
        intro i hi hyi
        have hi' : pred.a i = 2 := by
          simp [B] at hi
          exact hi
        have hyi' := (neg₂_dichotomy hi').mpr hyi
        simp [hi, hyi']
        symm; exact hyi
  }
  right; right; right; left
  constructor
  · obtain ⟨ζ, Pζ, hζ⟩ := pred.full range_0 (neg₂ (η range_0))
    have hdiff : ζ ≠ η := by
      by_contra h
      have := congrFun h range_0
      rw [hζ] at this
      apply neg₂_ne (η range_0)
      symm; assumption
    apply hB ζ hdiff Pζ
  use e
  constructor
  · intro i hi
    have : i ∈ B := by exact hi
    cases of_range_2' hi (η i)
    case inl h0 =>
      right
      simp [e, this, h0, neg₂]
      rfl
    case inr h1 =>
      left
      simp [e, this, h1, neg₂]
      rfl
  · intro i hi
    have : i∉ B := by
      by_contra! h
      simp [B] at h
      linarith
    simp [e, hi, this]

lemma trivial_for_2_of_trivial_for_1_exists_dict_cert (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2)
  {η} (Pη : pred.P η) (hη : h_all_none poly η)
  {i₀ σ₀ τ₀} (hi₀σ₀ : h_func poly i₀ σ₀ = some τ₀)
  {cη : Certificate pred}
  (hcη : ∀ i : cη.dom, (G_polymorphism htrivial hperm poly Pη).fs i = (fun _ => cη.ρ i)) :
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ) := by
  let Gη := G_polymorphism htrivial hperm poly Pη
  have Gηη i : Gη.fs i (η i) = η i := by
    simp [Gη, G_polymorphism, G_func, hη i]
  by_cases ∃ i σ, h_func poly i σ ≠ none ∧ h_func poly i σ ≠ some (η i)
  case pos h =>
    obtain ⟨i, σ, hiσ₁, hiσ₂⟩ := h
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp hiσ₁
    have hτη : τ ≠ η i := by
      rw [hτ] at hiσ₂
      contrapose! hiσ₂
      rw [hiσ₂]
    have hi : i ∉ cη.dom := by
      contrapose! hτη
      have Gητ : Gη.fs i σ = τ := G_of_h_some hτ
      replace Gηη := Gηη i
      rw [←Gητ, ←Gηη, congrFun (hcη ⟨i, hτη⟩) σ, congrFun (hcη ⟨i, hτη⟩) (η i)]
    let ζ := set_coord_to i σ η
    have Pζ : pred.P ζ := by
      apply cη.cert
      intro i'
      have hi' : i ≠ i' := by
        contrapose! hi
        rw [hi]
        exact i'.coe_prop
      simp [ζ, set_coord_to, hi']
      split
      case isTrue h => exfalso; apply hi'; symm; convert h
      case isFalse h =>
      rw [←congrFun (hcη i') (η i')]
      simp [G_polymorphism, G_func, hη i']
    have hζ_i : h_func poly i (ζ i) = some τ := by
      simp [ζ, set_coord_to]
      assumption
    have hζ_ne_i i' (hi' : i' ≠ i) : h_func poly i' (ζ i') = none := by
      simp [ζ, set_coord_to, hi']
      apply hη
    have : ¬ h_all_none poly ζ := by
      unfold h_all_none
      push_neg
      use i
      rw [hζ_i]
      simp
    obtain ⟨cζ, hcζ⟩ := certificate_of_not_h_all_none htrivial hperm Pζ this
    right; right; left
    use i, τ
    intro y Py
    apply cζ.cert
    intro i'
    by_cases i' = i
    case pos h =>
      subst h
      simp [set_coord_to]
      have := hcζ i'
      rw [hζ_i] at this
      apply Option.some_inj.mp
      exact this
    case neg h =>
      have := hζ_ne_i i' h
      rw [hcζ i'] at this
      simp at this
  case neg hrange =>
    push_neg at hrange
    let C := { i | ∀ σ, h_func poly i σ = none }
    have hCnotfull : i₀ ∉ C := by
      contrapose! hi₀σ₀
      simp only [C, mem_filter] at hi₀σ₀
      rw [hi₀σ₀ σ₀]
      simp
    by_cases ∃ i, i ∈ C ∨ pred.a i > 2
    case pos h =>
      obtain ⟨i, hi⟩ := h
      right; right; left
      use i₀, η i₀
      intro ζ Pζ
      let Gζ := G_polymorphism htrivial hperm poly Pζ
      cases htrivial Gζ
      case inl hdict =>
        exfalso
        replace hperm := hperm Gζ.fs hdict i
        cases hi
        case inl h_i_in_C =>
          have Gi σ : Gζ.fs i σ = ζ i := by
            simp [Gζ, G_polymorphism, G_func, h_i_in_C σ]
          have := hperm.1 (Eq.trans (Gi range_0) (Eq.symm (Gi range_1)))
          simp [range_0, range_1] at this
        case inr h_i_nbool =>
          have Gi σ : Gζ.fs i σ = ζ i ∨ Gζ.fs i σ = η i := by
            simp [Gζ, G_polymorphism, G_func]
            split
            case h_1 τ hsome =>
              right
              have : h_func poly i σ ≠ none := by
                apply Option.ne_none_iff_exists'.mpr
                use τ
              have := hrange i σ this
              rw [hsome] at this
              apply Option.some_inj.mp
              assumption
            case h_2 hnone =>
              left; rfl
          obtain ⟨σ₁, σ₂, h⟩ := php3 h_i_nbool Gi
          apply h.1
          apply hperm.1 h.2
      case inr hcert =>
        obtain ⟨c, hc⟩ := hcert
        apply c.cert
        intro i
        have hρ : c.ρ i = ζ i := by
          rw [←congrFun (hc i) (η i)]
          simp [Gζ, G_polymorphism, G_func, hη i]
        rw [hρ]
        unfold set_coord_to
        split
        case isFalse => rfl
        case isTrue h =>
        subst h
        simp [C] at hCnotfull
        obtain ⟨σ₁, σ₂, hσ⟩ := hCnotfull
        let σ : range (pred.a i) := ⟨σ₁, by apply mem_range.mpr; exact σ₂⟩
        have := hrange i σ hσ
        have hρ' : c.ρ i = η i := by
          rw [←congrFun (hc i) σ]
          simp [Gζ, G_polymorphism, G_func, this]
        rw [←hρ, hρ']
    case neg h =>
      push_neg at h
      have hbool i : pred.a i = 2 := by
        have := (h i).2
        have := pred.ha i
        linarith
      have hsome i : h_func poly i (neg₂ (η i)) = some (η i) := by
        apply hrange i
        have := (h i).1
        simp [C] at this
        obtain ⟨σ₁, σ₂, hσ⟩ := this
        push_neg at hσ
        let σ : range (pred.a i) := ⟨σ₁, by apply mem_range.mpr; exact σ₂⟩
        replace hσ : h_func poly i σ ≠ none := hσ
        convert hσ
        symm
        apply (neg₂_dichotomy (hbool i)).mp
        contrapose! hσ
        rw [hσ]
        apply hη
      let neg₂η i := neg₂ (η i)
      have hsome' i : h_func poly i (neg₂η i) = some (η i) := by
        convert hsome i
      have hP {ζ} (Pζ : pred.P ζ) (hζ : ζ ≠ neg₂η) i :
        pred.P (set_coord_to i (η i) ζ) := by
        let Gζ := G_polymorphism htrivial hperm poly Pζ
        have Gζnη i : Gζ.fs i (neg₂η i) = η i := by
          simp [Gζ, G_polymorphism, G_func, hsome' i]
        have Gζη i : Gζ.fs i (η i) = ζ i := by
          simp [Gζ, G_polymorphism, G_func, hη i]
        cases htrivial Gζ
        case inl hdict =>
          exfalso
          apply hζ
          ext i
          apply Subtype.coe_inj.mpr
          apply (neg₂_dichotomy (hbool i)).mp
          by_contra h
          rw [←Gζnη i, ←Gζη i] at h
          have := (hperm Gζ.fs hdict i).1 h
          simp [neg₂η] at this
          apply neg₂_ne (η i)
          assumption
        case inr hcert =>
          obtain ⟨c, hc⟩ := hcert
          apply c.cert
          intro i'
          have hζρ : ζ i' = c.ρ i' := by
            rw [←Gζη i']
            apply congrFun (hc i')
          have hηρ : η i' = c.ρ i' := by
            rw [←Gζnη i']
            apply congrFun (hc i')
          unfold set_coord_to
          split
          case isTrue h =>
            subst h
            assumption
          case isFalse =>
            assumption
      have hP' {ζ} (Pζ : pred.P ζ) (hζ : ζ ≠ neg₂η)
        (S : Finset (range pred.m)) :
        pred.P (fun i => if i ∈ S then η i else ζ i) := by
        induction S using Finset.induction_on
        case empty =>
          simp
          assumption
        case insert i' S' hi' hS' =>
          simp
          let χ := (fun i => if i ∈ S' then η i else ζ i)
          have : χ ≠ neg₂η := by
            contrapose! hζ
            funext i
            simp [χ] at hζ
            replace hζ := congrFun hζ i
            split at hζ
            case isTrue h =>
              simp [neg₂η] at hζ
              exfalso
              apply neg₂_ne (η i)
              assumption
            case isFalse h =>
              assumption
          convert hP hS' this i' with i
          unfold set_coord_to
          split
          case isTrue h =>
            cases h
            case inl h =>
              simp [h]
              subst h
              rfl
            case inr h =>
              simp [h]
              split
              case isTrue h =>
                subst h
                rfl
              case isFalse h =>
                rfl
          case isFalse h =>
            push_neg at h
            simp [h]
      have hP'' {ζ} (Pζ : pred.P ζ) (hζ : ζ ≠ neg₂η)
        {ξ} (hξ : ∀ ⦃i⦄, ζ i ≠ ξ i → ξ i = η i) : pred.P ξ := by
        let S : Finset _ := {i | ζ i ≠ ξ i}
        convert hP' Pζ hζ S with i
        split
        case isTrue h =>
          simp [S] at h
          apply hξ h
        case isFalse h =>
          simp [S] at h
          rw [h]
      let e : Polymorphism pred 2 :=
      {
        fs i x :=
        if x range_0 = neg₂η i ∧ x range_1 = neg₂η i then
          neg₂η i
        else
          η i
        app xs sat := by
          by_cases (xs · range_0) = neg₂η
          case pos hy =>
            replace hy := congrFun hy
            by_cases (xs · range_1) = neg₂η
            case pos hz =>
              replace hz := congrFun hz
              convert sat range_0 with i
              simp [hy i, hz i]
            case neg hz =>
              apply hP'' (sat range_1) hz
              intro i hi
              simp
              intro h0 h1
              simp [h0, h1] at hi
          case neg hy =>
            apply hP'' (sat range_0) hy
            intro i hi
            simp
            intro h0 h1
            simp [h0, h1] at hi
      }
      right; right; right; left
      constructor
      · use range_0, hbool range_0
      use e
      constructor
      · intro i hi
        cases of_range_2' hi (η i)
        case inl h0 =>
          left
          simp [e, h0, neg₂, neg₂η]
          rfl
        case inr h1 =>
          right
          simp [e, h1, neg₂, neg₂η]
          rfl
      · intro i hi
        have := hbool i
        exfalso
        linarith

lemma trivial_for_2_of_trivial_for_1_exists_dict (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2)
  {η} (Pη : pred.P η) (hη : h_all_none poly η)
  {i₀ σ₀ τ₀} (hi₀σ₀ : h_func poly i₀ σ₀ = some τ₀) :
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ) := by
  cases htrivial (G_polymorphism htrivial hperm poly Pη)
  case inl h =>
    apply trivial_for_2_of_trivial_for_1_exists_dict_dict <;> assumption
  case inr h =>
    obtain ⟨cη, hcη⟩ := h
    apply trivial_for_2_of_trivial_for_1_exists_dict_cert <;> assumption

-- putting everything together

lemma trivial_for_2_of_trivial_for_1_main (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2) :
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ) := by
  by_cases ∀ i σ, h_func poly i σ = none
  case pos h =>
    right; right; right; right
    intro y Py
    have hy : h_all_none poly y := by
      intro i
      apply h
    convert dictatorial_of_h_all_none htrivial Py hy with i σ
  case neg h =>
    push_neg at h
    obtain ⟨i₀, σ₀, hi₀σ₀⟩ := h
    obtain ⟨τ₀, hi₀σ₀⟩ := Option.ne_none_iff_exists'.mp hi₀σ₀
    by_cases ∃ y, pred.P y ∧ h_all_none poly y
    case pos h =>
      obtain ⟨η, Pη, hη⟩ := h
      apply trivial_for_2_of_trivial_for_1_exists_dict <;> assumption
    case neg h =>
      push_neg at h
      apply trivial_for_2_of_trivial_for_1_all_cert <;> assumption

def switch {type : Type} (x : range 2 → type) (i : range 2) :=
  if i = range_0 then x range_1 else x range_0

@[simp]
lemma switch_of_switch {type : Type} (x : range 2 → type) :
  switch (switch x) = x := by
  funext j
  cases of_range_2 j
  case inl hj => simp [switch, hj, range_0, range_1]
  case inr hj => simp [switch, hj, range_0, range_1]

lemma trivial_for_2_of_trivial_for_1_poly (pred : Predicate) (Φ : Set (format pred))
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ)
  (poly : Polymorphism pred 2) :
  is_dictatorship poly Φ ∨
  is_certificate poly ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  is_Latin_square_poly Φ poly := by
  let poly' : Polymorphism pred 2 :=
  {
    fs i x := poly.fs i (switch x),
    app xs sat := by
      let xs' i := switch (xs i)
      apply poly.app xs'
      intro j
      cases of_range_2 j
      all_goals simp [xs', switch]
      case inl hj => simp [hj]; apply sat
      case inr hj => simp [hj]; apply sat
  }
  cases trivial_for_2_of_trivial_for_1_main pred Φ hperm htrivial poly
  case inl h => left; exact h
  case inr h =>
    cases h
    case inl h => right; left; exact h
    case inr h =>
      cases h
      case inl h => right; right; left; exact h
      case inr h =>
        cases h
        case inl h => right; right; right; left; exact h
        case inr hlatin =>
          cases trivial_for_2_of_trivial_for_1_main pred Φ hperm htrivial poly'
          case inl h =>
            left
            obtain ⟨j, φ, hφ, hdict⟩ := h
            cases of_range_2 j
            case inl hj =>
              use range_1, φ, hφ
              intro i x
              have := hdict i (switch x)
              simp [poly', hj, switch] at this
              assumption
            case inr hj =>
              use range_0, φ, hφ
              intro i x
              have := hdict i (switch x)
              simp [poly', hj, switch] at this
              assumption
          case inr h =>
            cases h
            case inl h =>
              right; left
              obtain ⟨c, hc⟩ := h
              use c
              intro i x
              rw [←hc i (switch x)]
              simp [poly']
            case inr h =>
              cases h
              case inl h => right; right; left; exact h
              case inr h =>
                cases h
                case inl h => right; right; right; left; exact h
                case inr hlatin' =>
                  right; right; right; right
                  constructor <;> assumption

end ReductionTo1

open ReductionTo1 in
theorem trivial_for_2_of_trivial_for_1 {pred : Predicate} {Φ : Set (format pred)}
  (hperm : permutational Φ) (htrivial : trivial_for₁ pred Φ) :
  trivial_for pred Φ 2 ∨
  has_closure pred ∨
  has_AND_OR_poly pred ∨
  has_Latin_square_poly pred Φ := by
  by_cases trivial_for pred Φ 2
  case pos h => left; exact h
  case neg h =>
    right
    unfold trivial_for at h
    push_neg at h
    obtain ⟨poly, hdict, hcert⟩ := h
    cases trivial_for_2_of_trivial_for_1_poly pred Φ hperm htrivial poly
    case inl h => contradiction
    case inr h =>
      cases h
      case inl h => contradiction
      case inr h =>
        cases h
        case inl h => left; exact h
        case inr h =>
          right
          cases h
          case inl h => left; exact h
          case inr h => right; use poly

lemma is_Latin_square_of_is_Latin_square_poly {pred : Predicate}
  {Φ : Set (format pred)} (hperm : permutational Φ)
  {poly : Polymorphism pred 2} (hLatin : is_Latin_square_poly Φ poly)
  (i : range pred.m) : is_Latin_square (poly.fs i) := by
  constructor
  · intro σ
    obtain ⟨y, Py, hy⟩ := pred.full i σ
    rw [←hy]
    exact hperm _ (hLatin.1 y Py) i
  · intro σ
    obtain ⟨y, Py, hy⟩ := pred.full i σ
    rw [←hy]
    exact hperm _ (hLatin.2 y Py) i
