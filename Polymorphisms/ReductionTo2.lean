-- in this file the goal is to reduce the general case to the case n=2

import Polymorphisms.Basic
import Polymorphisms.Extend
import Polymorphisms.Restrict
import Polymorphisms.Classify
open Finset
open Classical

namespace ReductionTo2

-- classify functions on [a]^n into constant, non-constant dictator, and other
section f_classification

variable {a n : ℕ} [AtLeast1 a] (f : (range n → range a) → range a)

inductive f_type (a n : ℕ)
| const (τ : range a)
| dictator (j : range n) (φ : range a → range a)
| other

def const_input (σ : range a) (_ : range n) := σ

def f_constant (f : (range n → range a) → range a) :=
  ∀ x : range n → range a, f x = f (const_input range_0)

def φ_of_f (σ : range a) :=
  f (const_input σ)

def f_dictatorial (j : range n) :=
  ∀ x : range n → range a, f x = f (const_input (x j))

noncomputable def f_classify : f_type a n :=
  if f_constant f then
    .const (f (const_input range_0))
  else
    let coords : Finset _ := { i | f_dictatorial f i }
    if h : coords.Nonempty then
      .dictator (min' coords h) (φ_of_f f)
    else
      .other

lemma f_const_spec (τ : range a) :
  f_classify f = .const τ ↔ ∀ x, f x = τ := by
  constructor
  · intro hclassify x
    simp [f_classify] at hclassify
    split at hclassify
    case isTrue hconst =>
      rw [f_type.const.injEq] at hclassify
      rw [←hclassify]
      apply hconst
    case isFalse hnonconst =>
      split at hclassify <;> contradiction
  · intro hf
    have fconst : f_constant f := by
      intro x
      rw [hf x, hf (const_input range_0)]
    simp [f_classify, fconst]
    apply hf

lemma f_dictator_spec (f : (range n → range a) → range a)
  (j : range n) (φ : range a → range a) :
  f_classify f = .dictator j φ ↔
  ((∀ x, f x = φ (x j)) ∧ ∃ σ₁ σ₂, φ_classify φ = .nonconst σ₁ σ₂) := by
  constructor
  · intro hclassify
    simp [f_classify] at hclassify
    split at hclassify
    case isTrue => contradiction
    case isFalse hnonconst =>
    split at hclassify
    case isFalse => contradiction
    case isTrue hmin' =>
    rw [f_type.dictator.injEq] at hclassify
    have fdictatorial : f_dictatorial f j := by
      have jdef := Eq.symm hclassify.1
      have := min'_mem _ hmin'
      rw [←jdef] at this
      have := (mem_filter.mp this).2
      assumption
    have φdef : φ = φ_of_f f := by symm; exact hclassify.2
    have hf : ∀ x : range n → range a, f x = φ (x j) := by
      intro x
      simp [φdef, φ_of_f]
      apply fdictatorial
    constructor
    · exact hf
    · cases hφ : φ_classify φ with
      | const τ =>
        exfalso
        apply hnonconst
        simp [f_constant]
        intro x
        rw [hf x, hf (const_input range_0)]
        simp [const_input]
        have := (φ_const_spec φ τ).mp hφ
        rw [this (x j), this range_0]
      | nonconst σ₁ σ₂ =>
        use σ₁, σ₂
  · rintro ⟨hf, hφ⟩
    have hf' : ∀ σ : range a, f (const_input σ) = φ σ := by
      intro σ
      apply hf
    simp [f_classify]
    split
    case isTrue hconst =>
      exfalso
      simp [f_constant] at hconst
      obtain ⟨σ₁, σ₂, hσ⟩ := hφ
      apply φ_nonconst_spec hσ
      rw [←hf' σ₁, ←hf' σ₂, hconst (const_input σ₁), hconst (const_input σ₂)]
    case isFalse hnonconst =>
      split
      case isTrue hnonempty =>
        have fdictatorial := (mem_filter.mp (min'_mem _ hnonempty)).2
        let j' := (filter (fun x ↦ f_dictatorial f x) (range n).attach).min' hnonempty
        have hj' : j' = (filter (fun x ↦ f_dictatorial f x) (range n).attach).min' hnonempty := rfl
        rw [←hj'] at fdictatorial
        simp [fdictatorial]
        rw [←hj']
        simp [f_dictatorial] at fdictatorial
        constructor
        · by_contra hjj'
          obtain ⟨σ₁, σ₂, hσ⟩ := hφ
          apply φ_nonconst_spec hσ
          let y (k : range n) := if k = j then σ₁ else σ₂
          have h₁ : f y = φ σ₁ := by
            simp [hf y, y]
          have h₂ : f y = φ σ₂ := by
            simp [fdictatorial y, y, hjj', hf' σ₂]
          rw [←h₁, ←h₂]
        · funext σ
          simp [φ_of_f]
          rw [hf (const_input σ)]
          simp [const_input]
      case isFalse hempty =>
        exfalso
        apply hempty
        have : f_dictatorial f j := by
          simp [f_dictatorial]
          intro x
          rw [hf x, hf (const_input (x j))]
          simp [const_input]
        apply filter_nonempty_iff.mpr
        use j
        constructor
        · simp
        · assumption

lemma f_const_or_dictator
  {f : (range n → range a) → range a} {φ : range a → range a} {j : range n}
  (hf : ∀ x, f x = φ (x j)) :
  (φ_classify φ = .const (φ range_0) ∧ f_classify f = .const (φ range_0)) ∨
  ((∃ σ₁ σ₂, φ_classify φ = .nonconst σ₁ σ₂) ∧ f_classify f = .dictator j φ) := by
  cases hφ : φ_classify φ
  case const τ =>
    replace hφ := (φ_const_spec φ τ).mp hφ
    left
    constructor
    · congr
      rw [hφ range_0]
    · apply (f_const_spec _ _).mpr
      intro x
      rw [hf x, hφ (x j), hφ range_0]
  case nonconst σ₁ σ₂ =>
    right
    constructor
    · use σ₁, σ₂
    apply (f_dictator_spec _ _ _).mpr
    constructor
    · assumption
    · use σ₁, σ₂

end f_classification

-- lemmas for the induction
section induction_lemmas

-- need n ≥ 1 for technical reasons (but can assume n ≥ 2 if need be)
variable {pred : Predicate} {Φ : Set (format pred)} {n : ℕ}

noncomputable def h_func (poly : Polymorphism pred (n+1)) (i : range pred.m)
  (σ : range (pred.a i)) : Option (range (pred.a i) → range (pred.a i)) :=
  match f_classify (fun x => poly.fs i (extend_input_by x σ)) with
  | .const τ => some (fun _ => τ)
  | .dictator _ φ => some φ
  | .other => none

lemma h_constant {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ τ : range (pred.a i)} :
  h_func poly i σ = some (fun _ => τ) ↔ (∀ x, poly.fs i (extend_input_by x σ) = τ) := by
  constructor
  · intro h
    cases hf : f_classify (fun x => poly.fs i (extend_input_by x σ))
    case const τ' =>
      simp [h_func, hf] at h
      have hτ' : τ' = τ := calc
        τ' = (fun (_ : range (pred.a i)) => τ') range_0 := rfl
        _  = (fun (_ : range (pred.a i)) => τ ) range_0 := by rw [h]
        _ = τ := rfl
      rw [hτ'] at hf
      apply (f_const_spec _ τ).mp
      assumption
    case dictator _ φ =>
      exfalso
      simp [h_func, hf] at h
      obtain ⟨σ₁, σ₂, hφ⟩ := ((f_dictator_spec _ _ _).mp hf).2
      apply φ_nonconst_spec hφ
      simp [h]
    case other =>
      simp [h_func, hf] at h
  · intro h
    have hf := (f_const_spec (fun x => poly.fs i (extend_input_by x σ)) τ).mpr h
    simp [h_func, hf]

lemma h_dictatorial {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ : range (pred.a i)} {j : range n} {φ : range (pred.a i) → range (pred.a i)}
  (h : ∀ x, poly.fs i (extend_input_by x σ) = φ (x j)) :
  h_func poly i σ = some φ := by
  cases f_const_or_dictator h
  case inl h =>
    obtain ⟨hφ, hf⟩ := h
    simp [h_func, hf]
    funext σ
    symm
    apply (φ_const_spec _ _).mp hφ
  case inr h =>
    obtain ⟨hφ, hf⟩ := h
    simp [h_func, hf]

noncomputable def j_coord [AtLeast1 n] (poly : Polymorphism pred (n+1)) (i : range pred.m)
  (σ : range (pred.a i)) : range n :=
  match f_classify (fun x => poly.fs i (extend_input_by x σ)) with
  | .const _ => range_0
  | .dictator j _ => j
  | .other => range_0

lemma f_of_h_some_nonconst [AtLeast1 n] {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ : range (pred.a i)} {φ : range (pred.a i) → range (pred.a i)}
  {σ₁ σ₂ : range (pred.a i)} (hφ : φ_classify φ = .nonconst σ₁ σ₂)
  (h : h_func poly i σ = some φ) :
  ∀ x, poly.fs i (extend_input_by x σ) = φ (x (j_coord poly i σ)) := by
  cases hf : f_classify (fun x => poly.fs i (extend_input_by x σ))
  all_goals simp [h_func, hf] at h
  case const τ =>
    exfalso
    apply φ_nonconst_spec hφ
    rw [←h]
  case dictator j ψ =>
    convert ((f_dictator_spec _ _ _).mp hf).1
    symm
    assumption
    unfold j_coord
    simp [hf]

lemma f_of_h_nonconst [AtLeast1 n] {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ : range (pred.a i)} {φ : range (pred.a i) → range (pred.a i)}
  (hφ : φ_const φ = false)
  (h : h_func poly i σ = some φ) :
  ∀ x, poly.fs i (extend_input_by x σ) = φ (x (j_coord poly i σ)):= by
  cases hφ' : φ_classify φ
  case const _ =>
    exfalso
    contrapose! hφ
    simp [φ_const, hφ']
  case nonconst σ₁ σ₂ =>
    apply f_of_h_some_nonconst <;> assumption

variable {a : ℕ} [AtLeast2 a]

def other_func (φ : Option (range a → range a)) (σ : range a) : range a :=
  match φ with
  | some ψ =>
    if ψ range_0 = range_0 then
      if σ = range_0 then
        range_1
      else
        range_0
    else
      σ
  | none => σ

lemma other_func_different (φ : range a → range a) :
  φ ≠ other_func (some φ) := by
  by_contra h
  suffices h' : φ range_0 ≠ other_func (some φ) range_0 by
    apply h'
    rw [←h]
  simp [other_func]
  split
  case isTrue hψ =>
    rw [hψ]
    simp [range_0, range_1]
  case isFalse hψ =>
    assumption

lemma other_func_ne_const (φ : Option (range a → range a)) (τ : range a) :
  ¬ other_func φ = fun _ => τ := by
  suffices h : other_func φ range_0 ≠ other_func φ range_1 by
    contrapose! h
    simp [h]
  simp [other_func]
  split
  split
  all_goals simp [range_0, range_1]

def dummy₀ (σ : range a) : range a := σ

def dummy₁ (σ : range a) : range a :=
  if σ = range_0 then
    range_1
  else
    range_0

lemma dummy_different (a : ℕ) [AtLeast2 a] : @dummy₀ a ≠ dummy₁ := by
  by_contra h
  have : @dummy₀ a range_1 ≠ dummy₁ range_1 := by
    simp [dummy₀, dummy₁, range_0, range_1]
  apply this
  rw [h]

lemma dummy₀_ne_const {a : ℕ} [AtLeast2 a] (τ : range a) : dummy₀ ≠ fun _ => τ := by
  suffices h : dummy₀ range_0 ≠ dummy₀ range_1 by
    contrapose! h
    rw [h]
  simp [dummy₀, range_0, range_1]

lemma dummy₁_ne_const {a : ℕ} [AtLeast2 a] (τ : range a) : dummy₁ ≠ fun _ => τ := by
  suffices h : dummy₁ range_0 ≠ dummy₁ range_1 by
    contrapose! h
    rw [h]
  simp [dummy₁, range_0, range_1]

noncomputable def g'_func (poly : Polymorphism pred (n+1)) (i : range pred.m)
  (σ : range (pred.a i)) : (range (pred.a i) → range (pred.a i)) :=
  let h := h_func poly i
  match h σ with
  | some φ => φ
  | none =>
    let defined : Finset _ := { σ | Option.isSome (h σ) }
    if hnonempty : defined.Nonempty then
      let σ₀ := min' defined hnonempty
      other_func (h σ₀)
    else
      if σ = range_0 then
        dummy₀
      else
        dummy₁

noncomputable def g_func (poly : Polymorphism pred (n+1)) (i : range pred.m)
  (x : range 2 → range (pred.a i)) : range (pred.a i) :=
  g'_func poly i (x range_0) (x range_1)

lemma g'_of_some_φ {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)} {σ : range (pred.a i)}
  (h : h_func poly i σ = some φ) :
  g'_func poly i σ = φ := by
  simp [g'_func, h]

lemma g_of_some_φ {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)} (x : range 2 → range (pred.a i))
  (h : h_func poly i (x range_0) = some φ) :
  g_func poly i x = φ (x range_1) := by
  simp [g_func, g'_func, h]

lemma h_of_g' {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ : range (pred.a i)} {φ : range (pred.a i) → range (pred.a i)}
  (h : g'_func poly i σ = φ) :
  h_func poly i σ = some φ ∨ h_func poly i σ = none := by
  cases hh : h_func poly i σ
  all_goals simp [g'_func, hh] at h
  case none => right; rfl
  case some ψ => left; congr

noncomputable def g_polymorphism (poly : Polymorphism pred (n+1))
  (hind : trivial_for pred Φ n) : Polymorphism pred 2 :=
{
  fs := g_func poly,
  app xs sat := by
    let rest := restrict_polymorphism poly (sat range_0)
    cases hind rest
    case _ hdictatorship =>
      obtain ⟨j, φ, hφ, hf⟩ := hdictatorship
      have hh i := h_dictatorial (hf i)
      have hg i := g_of_some_φ (xs i) (hh i)
      conv => congr; ext i; rw [hg i]
      let ys i (j : range (n+1)) :=
        if j < range_last then xs i range_1 else xs i range_0
      have Pys := poly.app ys ?_
      case refine_1 =>
        intro j
        by_cases hj : j < range_last
        all_goals simp [ys, hj]; apply sat
      convert Pys with i
      calc
        φ i (xs i range_1) = φ i (ys i (extend_index (by omega) j)) := by
          simp [ys, extend_index, range_last, mem_range.mp j.coe_prop]
        _ = rest.fs i (shorten_input (ys i)) := by
          symm
          apply hf
        _ = poly.fs i (ys i) := by
          simp [rest, restrict_polymorphism]
          congr
          have : ys i (range_last) = xs i range_0 := by
            simp [ys]
          rw [←this]
          simp
    case _ hcertificate =>
      obtain ⟨cert, hcert⟩ := hcertificate
      have hh i := h_constant.mpr (hcert i)
      have hg (i : cert.dom) := g_of_some_φ (xs i) (hh i)
      apply cert.cert
      assumption
}

lemma g'_const {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {σ τ : range (pred.a i)}
  (hdictator : g'_func poly i σ = fun _ => τ) :
  h_func poly i σ = some (fun _ => τ) := by
  cases hf : f_classify (fun x => poly.fs i (extend_input_by x σ))
  case const τ' =>
    simp [h_func, hf]
    simp [g'_func, h_func, hf] at hdictator
    assumption
  case dictator _ φ =>
    exfalso
    obtain ⟨σ₁, σ₂, hφ⟩ := ((f_dictator_spec _ _ φ).mp hf).2
    apply φ_nonconst_spec hφ
    simp [g'_func, h_func, hf] at hdictator
    simp [hdictator]
  case other =>
    exfalso
    have hh : h_func poly i σ = none := by
      simp [h_func, hf]
    simp [g'_func, hh] at hdictator
    split at hdictator
    case isTrue =>
      apply @other_func_ne_const (pred.a i) _ _
      exact hdictator
    case isFalse =>
      split at hdictator
      case isTrue =>
        apply dummy₀_ne_const τ
        assumption
      case isFalse =>
        apply dummy₁_ne_const τ
        assumption

lemma g_dictator_0 {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)}
  (hdictator : ∀ x, g_func poly i x = φ (x range_0)) :
  ∀ x, poly.fs i x = φ (x range_last) := by
  intro x
  let σ := x range_last
  have : g'_func poly i σ = fun _ => φ σ := by
    funext τ
    apply hdictator (cons_input σ τ)
  replace := g'_const this
  replace := h_constant.mp this (shorten_input x)
  simp [σ] at this
  assumption

lemma g_dictator_1_const {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)}
  (hφ : φ_const φ = true)
  (hdictator : ∀ x, g_func poly i x = φ (x range_1)) :
  ∀ x, poly.fs i x = φ range_0 := by
  replace hφ := φ_classify_of_φ_const hφ
  let τ := φ range_0
  let ψ (_ : range (pred.a i)) := τ
  have : ∀ x, g_func poly i x = ψ (x range_0) := by
    intro x
    rw [hdictator x, (φ_const_spec φ τ).mp hφ]
  have := g_dictator_0 this
  intro x
  rw [this x]

lemma g_dictator_1_nonconst [AtLeast1 n] {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)}
  (hφ : φ_const φ = false)
  (hdictator : ∀ x, g_func poly i x = φ (x range_1)) (σ : range (pred.a i)) :
  ∀ x, poly.fs i (extend_input_by x σ) = φ (x (j_coord poly i σ)) := by
  have hg' : ∀ σ, g'_func poly i σ = φ := by
    intro σ
    funext τ
    apply hdictator (cons_input σ τ)
  have hh : h_func poly i σ = some φ := by
    cases h_of_g' (hg' σ)
    case inl => assumption
    case inr hnone =>
      exfalso
      have hg'σ := hg' σ
      simp [g'_func, hnone] at hg'σ
      split at hg'σ
      case isTrue hnonempty =>
        let σ₀ := min' _ hnonempty
        have hσ₀ : (h_func poly i σ₀).isSome :=
          (mem_filter.mp (min'_mem _ hnonempty)).2
        replace hg'σ : other_func (h_func poly i σ₀) = φ := hg'σ
        cases h : h_func poly i σ₀
        case none =>
          rw [h, Option.isSome] at hσ₀
          contradiction
        case some ψ =>
          have h' := g'_of_some_φ h
          have := other_func_different ψ
          apply this
          rw [←h, hg'σ, ←h', hg' σ₀]
      case isFalse hempty =>
        have := dummy_different (pred.a i)
        apply this
        have hnone : ∀ σ, h_func poly i σ = none := by
          replace hempty := not_nonempty_iff_eq_empty.mp hempty
          replace hempty := filter_eq_empty_iff.mp hempty
          intro σ
          suffices h : ¬(h_func poly i σ).isSome = true by
            cases h' : h_func poly i σ
            case none => rfl
            case some =>
              exfalso
              contrapose! h
              simp [h']
          apply hempty
          simp
        have hg'_0 := hg' range_0
        have hg'_1 := hg' range_1
        simp [g'_func, hnone range_0, hempty] at hg'_0
        simp [g'_func, hnone range_1, hempty] at hg'_1
        simp [range_0, range_1] at hg'_1
        rw [hg'_0, hg'_1]
  apply f_of_h_nonconst hφ hh

lemma g_dictator_1_nonconst' [AtLeast1 n] {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)}
  (hφ : φ_const φ = false)
  (hdictator : ∀ x, g_func poly i x = φ (x range_1)) :
  ∀ x, poly.fs i x = φ ((shorten_input x) (j_coord poly i (x range_last))) := by
  intro x
  convert g_dictator_1_nonconst hφ hdictator (x range_last) (shorten_input x)
  simp

def const_vector {i : range pred.m} (σ : range (pred.a i)) {len : ℕ} (_ : range len) := σ

lemma g_dictator_1 [AtLeast1 n] {poly : Polymorphism pred (n+1)} {i : range pred.m}
  {φ : range (pred.a i) → range (pred.a i)}
  (hdictator : ∀ x, g_func poly i x = φ (x range_1)) σ :
  poly.fs i (const_vector σ) = φ σ := by
  by_cases hφ : φ_const φ
  · rw [g_dictator_1_const hφ hdictator (const_vector σ)]
    rw [(φ_const_spec _ _).mp (φ_classify_of_φ_const hφ) σ]
  · rw [g_dictator_1_nonconst' (by simp [hφ]) hdictator (const_vector σ)]
    simp [const_vector, shorten_input]

end induction_lemmas

-- inductive step
section induction

variable {pred : Predicate} {Φ : Set (format pred)} {n : ℕ} (poly : Polymorphism pred (n+1))

variable {htrivial : trivial_for pred Φ n}

lemma trivial_of_trivial_induction_dictatorship_0
  (φ : format pred) (φ_in_Φ : φ ∈ Φ)
  (hdict : ∀ i x, (g_polymorphism poly htrivial).fs i x = φ i (x range_0)) :
  is_dictatorship poly Φ := by
  let g := g_polymorphism poly htrivial
  use range_last, φ, φ_in_Φ
  intro i
  apply g_dictator_0 (hdict i)

lemma trivial_of_trivial_induction_certificate (c : Certificate pred)
  (hc : ∀ i : c.dom, ∀ x, (g_polymorphism poly htrivial).fs i x = c.ρ i) :
  is_certificate poly := by
  let g := g_polymorphism poly htrivial
  use c
  intro i
  let φ (_ : range (pred.a i)) := c.ρ i
  replace hc : ∀ x, g.fs i x = φ (x range_0) := hc i
  apply g_dictator_0 hc

def nonconst_coords (φ : format pred) : Finset (range pred.m) :=
  { i : range pred.m | φ_const (φ i) = false}

def nonconst_coords_same [AtLeast1 n] (φ : format pred) (poly : Polymorphism pred (n+1)) :=
  ∃ j, ∀ (i : nonconst_coords φ) σ, j_coord poly i σ = j

def nonconst_coords_nonempty_of_not_same [AtLeast1 n] {φ : format pred} {poly : Polymorphism pred (n+1)}
  (hnotsame : ¬ nonconst_coords_same φ poly) :
  (nonconst_coords φ).Nonempty := by
  by_contra A_Empty
  replace A_Empty := not_nonempty_iff_eq_empty.mp A_Empty
  apply hnotsame
  use range_0
  intro i
  exfalso
  rw [A_Empty] at i
  apply not_mem_empty _
  exact i.prop

lemma trivial_of_trivial_induction_dictatorship_1_same [AtLeast1 n]
  (φ : format pred) (φ_in_Φ : φ ∈ Φ)
  (hdict : ∀ i x, (g_polymorphism poly htrivial).fs i x = φ i (x range_1))
  (hsame : nonconst_coords_same φ poly) :
  is_dictatorship poly Φ := by
  let A := nonconst_coords φ
  let j :=
    if hnonempty : A.Nonempty then
      j_coord poly (min' A hnonempty) range_0
    else
      range_0
  replace hj : ∀ i : A, ∀ σ, j_coord poly i σ = j := by
    by_cases hA : A.Nonempty
    case pos =>
      obtain ⟨j', hj'⟩ := hsame
      convert hj'
      simp [j, hA]
      let i : A := ⟨min' A hA, ?_⟩
      apply hj' i range_0
      exact min'_mem A hA
    case neg =>
      have := not_nonempty_iff_eq_empty.mp hA
      intro i
      simp [this] at i
      exfalso
      exact i.prop
  let j' : range (n + 1) := extend_index (by simp) j
  use j'
  use φ
  constructor
  assumption
  intro i
  cases hφ : φ_const (φ i)
  case true =>
    have hφ' := φ_classify_of_φ_const hφ
    replace hφ' := (φ_const_spec (φ i) _).mp hφ'
    conv =>
      intro x; rhs
      rw [hφ' (x j')]
    apply g_dictator_1_const hφ (hdict i)
  case false =>
    intro x
    have := g_dictator_1_nonconst hφ (hdict i) (x range_last) (shorten_input x)
    simp at this
    rw [this]
    congr
    let iA : A := ⟨i, by simp [A, nonconst_coords]; assumption⟩
    exact hj iA (x range_last)

noncomputable def active_j [AtLeast1 n] (φ : format pred) (poly : Polymorphism pred (n+1))
  (y : (i : range pred.m) → range (pred.a i)) :=
  image (fun i => j_coord poly i (y i)) (nonconst_coords φ)

def exists_bad_y [AtLeast1 n] (φ : format pred) (poly : Polymorphism pred (n+1)) :=
  ∃ y, pred.P y ∧ #(active_j φ poly y) > 1

def all_y_good [AtLeast1 n] (φ : format pred) (poly : Polymorphism pred (n+1)) :=
  ∀ ⦃y⦄, pred.P y → ∃ j, ∀ i : nonconst_coords φ, j_coord poly i (y i) = j

lemma exists_bad_y_or_all_y_good [AtLeast1 n] (φ : format pred) (poly : Polymorphism pred (n+1)) :
  exists_bad_y φ poly ∨ all_y_good φ poly := by
  by_cases hexists : exists_bad_y φ poly
  · left; assumption
  right
  simp [exists_bad_y] at hexists
  intro y Py
  have hcard := hexists y Py
  match hcard' : #(active_j φ poly y) with
  | 0 =>
    have := card_eq_zero.mp hcard'
    have := image_eq_empty.mp this
    use range_0
    intro i
    rw [this] at i
    exfalso
    apply not_mem_empty
    exact i.coe_prop
  | 1 =>
    obtain ⟨j, hj⟩ := card_eq_one.mp hcard'
    use j
    intro i
    have h : j_coord poly i (y i) ∈ active_j φ poly y := by
      apply mem_image_of_mem
      exact i.coe_prop
    rw [hj] at h
    exact mem_singleton.mp h
  | n+2 =>
    exfalso
    rw [hcard'] at hcard
    linarith [hcard]

noncomputable def other {type type' : Type} (σ : type') (τ₁ τ₂ : type) (f : type → type') :=
  if σ = f τ₁ then τ₂ else τ₁

lemma other_diff {type type' : Type} (σ : type') {τ₁ τ₂ : type} (f : type → type')
  (h : f τ₁ ≠ f τ₂) : f (other σ τ₁ τ₂ f) ≠ σ := by
  unfold other
  split
  case isTrue htrue =>
    rw [htrue]
    symm
    exact h
  case isFalse hfalse =>
    push_neg at hfalse
    symm
    exact hfalse

lemma trivial_of_trivial_induction_dictatorship_1_exists_bad_y [AtLeast1 n]
  (φ : format pred)
  (hdict : ∀ i x, (g_polymorphism poly htrivial).fs i x = φ i (x range_1))
  (hbad : exists_bad_y φ poly) :
  is_certificate poly := by
  obtain ⟨y, Py, hy⟩ := hbad
  let poly_y := restrict_polymorphism poly Py
  cases htrivial poly_y
  case inl hdictator =>
    obtain ⟨j, φ', φ'_in_Φ, hdictator⟩ := hdictator
    obtain ⟨j', hj', j_ne_j'⟩ := exists_ne_of_one_lt_card hy j
    obtain ⟨i, hi, hij'⟩ := mem_image.mp hj'
    have hφconst : φ_const (φ i) = false := (mem_filter.mp hi).2
    obtain ⟨σ₁, σ₂, hφ⟩ := φ_classify_of_not_φ_const hφconst
    replace hφ := φ_nonconst_spec hφ
    let σ := other (φ' i range_0) σ₁ σ₂ (φ i ·)
    let x k := if k = j then range_0 else σ
    have xj : x j = range_0 := by simp [x]
    have xj' : x j' = σ := by simp [x, j_ne_j']
    have fx := hdictator i x
    have fx' := g_dictator_1_nonconst hφconst (hdict i) (y i) x
    rw [hij'] at fx'
    simp [poly_y, restrict_polymorphism] at fx
    rw [xj] at fx
    rw [xj'] at fx'
    rw [fx] at fx'
    simp [σ] at fx'
    exfalso
    apply other_diff (φ' i range_0) (φ i ·) hφ
    symm
    assumption
  case inr hc =>
    obtain ⟨c, hc⟩ := hc
    have hconst : ∀ i : c.dom, φ_const (φ i) = true := by
      intro i
      by_contra hnonconst
      push_neg at hnonconst
      replace hnonconst := Bool.eq_false_iff.mpr hnonconst
      obtain ⟨σ₁, σ₂, hφ⟩ := φ_classify_of_not_φ_const hnonconst
      replace hφ := φ_nonconst_spec hφ
      let σ := other (c.ρ i) σ₁ σ₂ (φ i ·)
      let x (j : range n) := σ
      have fx := hc i x
      have fx' := g_dictator_1_nonconst hnonconst (hdict i) (y i) x
      simp [poly_y, restrict_polymorphism] at fx
      conv at fx' =>
        rhs
        simp [x]
      rw [fx] at fx'
      simp [σ] at fx'
      apply other_diff (c.ρ i) (φ i ·) hφ
      symm
      assumption
    replace hconst' : ∀ i : c.dom, φ i (range_0) = c.ρ i := by
      intro i
      have hφ := φ_classify_of_φ_const (hconst i)
      let x (j : range n) : range (pred.a i) := range_0
      have fx := hc i x
      have fx' := g_dictator_1_const (hconst i) (hdict i) (extend_input_by x (y i))
      rw [←fx, ←fx']
      simp [poly_y, restrict_polymorphism]
    use c
    intro i
    convert g_dictator_1_const (hconst i) (hdict i)
    symm
    exact hconst' i

lemma trivial_of_trivial_induction_dictatorship_1_all_y_good [AtLeast1 n]
  (φ : format pred)
  (base_case : trivial_for pred Φ 2)
  (hdict : ∀ i x, (g_polymorphism poly htrivial).fs i x = φ i (x range_1))
  (hnotsame : ¬nonconst_coords_same φ poly)
  (hgood : all_y_good φ poly) :
  is_certificate poly := by
  have hgood' {y} (Py : pred.P y) (i₁ i₂ : nonconst_coords φ) :
    j_coord poly i₁ (y i₁) = j_coord poly i₂ (y i₂) := by
    obtain ⟨j, hj⟩ := hgood Py
    rw [hj i₁, hj i₂]
  obtain ⟨y₀, Py₀, _⟩ := pred.full range_0 range_0
  obtain ⟨j₀, hj₀⟩ := hgood Py₀
  obtain ⟨i₀, hi₀⟩ := (nonconst_coords_nonempty_of_not_same hnotsame).exists_mem
  replace i₀ : nonconst_coords φ := ⟨i₀, hi₀⟩
  clear hi₀
  let A₀ (i : nonconst_coords φ) : Finset _ := { σ | j_coord poly i σ = j₀ }
  have A₀_nonempty i : y₀ i ∈ A₀ i := by
    apply mem_filter.mpr
    constructor
    · simp
    · apply hj₀
  have A₀_nonfull₀ : ∃ σ, σ ∉ A₀ i₀ := by
    contrapose! hnotsame
    conv at hnotsame =>
      intro σ
      simp [A₀]
    use j₀
    intro i' σ
    obtain ⟨z, Pz, hz⟩ := pred.full i' σ
    rw [←hz]
    rw [hgood' Pz i' i₀]
    apply hnotsame
  obtain ⟨y₁, Py₁, hy₁⟩ := pred.full i₀ (choose A₀_nonfull₀)
  have same_type {y} (Py : pred.P y) :
    (∀ i : nonconst_coords φ, y i ∈ A₀ i) ∨
    (∀ i : nonconst_coords φ, y i ∉ A₀ i) := by
    by_cases h : y i₀ ∈ A₀ i₀
    · left
      intro i
      apply mem_filter.mpr
      constructor; simp
      rw [←(mem_filter.mp h).2]
      apply hgood' Py
    · right
      intro i
      contrapose! h
      apply mem_filter.mpr
      constructor; simp
      rw [←(mem_filter.mp h).2]
      apply hgood' Py
  have A₀_nonfull i : y₁ i ∉ A₀ i := by
    cases same_type Py₁
    case inr h => apply h
    case inl h =>
      exfalso
      apply choose_spec A₀_nonfull₀
      rw [←hy₁]
      apply h
  have φ_poly {y} (Py : pred.P y) : pred.P (fun i => φ i (y i)) := by
    let xs i : range (n + 1) → range _ := const_vector (y i)
    have sat j : pred.P (xs · j) := by exact Py
    have := poly.app xs sat
    conv at this =>
      congr
      ext i
      simp [xs]
      rw [g_dictator_1 (hdict i)]
    assumption
  let χ : Polymorphism pred 2 :=
  {
    fs i x :=
      if hi : i ∈ nonconst_coords φ then
        if x range_0 ∈ A₀ ⟨i, hi⟩ then
          φ i (x range_0)
        else
          φ i (x range_1)
      else
        φ i range_0
    app xs sat := by
      have hsimp i j : (if i ∈ nonconst_coords φ then φ i (xs i j) else φ i range_0) = φ i (xs i j) := by
        split
        case isTrue => rfl
        case isFalse hconst =>
          symm
          apply (φ_const_spec _ _).mp
          apply φ_classify_of_φ_const
          contrapose! hconst
          apply mem_filter.mpr
          constructor; simp
          exact eq_false_of_ne_true hconst
      cases h : same_type (sat range_0)
      all_goals simp [*]
  }
  cases base_case χ
  case inl hχ =>
    rcases hχ with ⟨j, φ', hφ', hχ⟩
    replace hχ := hχ i₀
    obtain ⟨σ₁, σ₂, hσ₁σ₂⟩ := φ_classify_of_not_φ_const (mem_filter.mp i₀.coe_prop).2
    replace hσ₁σ₂ := φ_nonconst_spec hσ₁σ₂
    obtain ⟨z₁, Pz₁, hz₁⟩ := pred.full i₀ σ₁
    obtain ⟨z₂, Pz₂, hz₂⟩ := pred.full i₀ σ₂
    have χ₀₁ := hχ (cons_input (y₀ i₀) (z₁ i₀))
    have χ₀₂ := hχ (cons_input (y₀ i₀) (z₂ i₀))
    have χ₁₁ := hχ (cons_input (y₁ i₀) (z₁ i₀))
    have χ₁₂ := hχ (cons_input (y₁ i₀) (z₂ i₀))
    simp [χ, cons_input, range_0, range_1, A₀_nonempty i₀] at χ₀₁
    simp [χ, cons_input, range_0, range_1, A₀_nonempty i₀] at χ₀₂
    simp [χ, cons_input, range_0, range_1, A₀_nonfull i₀] at χ₁₁
    simp [χ, cons_input, range_0, range_1, A₀_nonfull i₀] at χ₁₂
    exfalso
    cases of_range_2 j
    case inl hj =>
      simp [hj] at hχ
      simp [hj, range_0, hz₁] at χ₁₁
      simp [hj, range_0, hz₂] at χ₁₂
      apply hσ₁σ₂
      rw [χ₁₁, χ₁₂]
    case inr hj =>
      simp [hj] at hχ
      simp [hj, range_1, hz₁] at χ₀₁
      simp [hj, range_1, hz₂] at χ₀₂
      simp [hj, range_1, hz₁] at χ₁₁
      simp [hj, range_1, hz₂] at χ₁₂
      by_cases h : φ i₀ (y₀ i₀) = φ i₀ σ₁
      · apply hσ₁σ₂
        rw [h] at χ₀₂
        rw [χ₀₂, χ₁₂]
      · apply h
        rw [χ₀₁, χ₁₁]
  case inr hχ =>
    rcases hχ with ⟨c, hc⟩
    use c
    intro i
    have hconst : φ_const (φ i) = true := by
      by_contra hnonconst
      replace hnonconst := eq_false_of_ne_true hnonconst
      have hnonconst' : ↑i ∈ nonconst_coords φ := by
        apply mem_filter.mpr
        constructor; simp; assumption
      obtain ⟨σ₁, σ₂, hσ₁σ₂⟩ := φ_classify_of_not_φ_const hnonconst
      apply φ_nonconst_spec hσ₁σ₂
      obtain ⟨z₁, Pz₁, hz₁⟩ := pred.full i σ₁
      obtain ⟨z₂, Pz₂, hz₂⟩ := pred.full i σ₂
      have χ₁ := hc i (cons_input (y₁ i) (z₁ i))
      have χ₂ := hc i (cons_input (y₁ i) (z₂ i))
      simp [χ, cons_input, hnonconst', range_0, range_1, A₀_nonfull ⟨i, hnonconst'⟩, hz₁] at χ₁
      simp [χ, cons_input, hnonconst', range_0, range_1, A₀_nonfull ⟨i, hnonconst'⟩, hz₂] at χ₂
      rw [χ₁, χ₂]
    convert g_dictator_1_const hconst (hdict i)
    rw [←hc i (cons_input (y₀ i) (y₀ i))]
    simp [χ, cons_input]
    intro h
    simp [nonconst_coords, hconst] at h

lemma trivial_of_trivial_induction_dictatorship_1 [AtLeast1 n]
  (φ : format pred) (φ_in_Φ : φ ∈ Φ)
  (base_case : trivial_for pred Φ 2)
  (hdict : ∀ i x, (g_polymorphism poly htrivial).fs i x = φ i (x range_1)) :
  is_dictatorship poly Φ ∨ is_certificate poly := by
  by_cases hsame : ∃ j, ∀ i : nonconst_coords φ, ∀ σ, j_coord poly i σ = j
  · left
    apply trivial_of_trivial_induction_dictatorship_1_same <;> assumption
  · right
    cases exists_bad_y_or_all_y_good φ poly
    · apply trivial_of_trivial_induction_dictatorship_1_exists_bad_y <;> assumption
    · apply trivial_of_trivial_induction_dictatorship_1_all_y_good <;> assumption

lemma trivial_of_trivial_induction [AtLeast1 n]
  (base_case : trivial_for pred Φ 2) (htrivial : trivial_for pred Φ n) :
  trivial_for pred Φ (n + 1) := by
  intro poly
  cases base_case (g_polymorphism poly htrivial)
  case inl g_is_dictatorship =>
    obtain ⟨j, φ, ⟨φ_in_Φ, g_is_dictatorship⟩⟩ := g_is_dictatorship
    cases of_range_2 j
    case inl j_0 =>
      rw [j_0] at g_is_dictatorship
      left
      apply trivial_of_trivial_induction_dictatorship_0 <;> assumption
    case inr j_1 =>
      rw [j_1] at g_is_dictatorship
      apply trivial_of_trivial_induction_dictatorship_1 <;> assumption
  case inr g_is_certificate =>
    right
    obtain ⟨c, hc⟩ := g_is_certificate
    apply trivial_of_trivial_induction_certificate <;> assumption

end induction

end ReductionTo2

open ReductionTo2 in
theorem trivial_iff_trivial_for_2 (pred : Predicate) (Φ : Set (format pred)) :
  (∀ n, trivial_for pred Φ n) ↔ (trivial_for pred Φ 2) := by
  constructor
  · intro h; exact h 2
  intro base_case
  intro n
  cases n
  case zero =>
    apply trivial_of_trivial_larger base_case
    linarith
  case succ n' =>
  induction n'
  case zero =>
    apply trivial_of_trivial_larger base_case
    linarith
  case succ =>
    apply trivial_of_trivial_induction base_case
    assumption
