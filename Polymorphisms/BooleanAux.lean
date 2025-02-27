-- in this file we prove auxiliary results about the Boolean setting

import Polymorphisms.BooleanReductions
open Finset

-- functions on one bit

def C0 (_ : range 2) := b0
def C1 (_ : range 2) := b1
def ID (b : range 2) := b
def NEG (b : range 2) := if b = b0 then b1 else b0

lemma NEG_ne a : a ≠ NEG a := by
  cases of_range_2B a <;> simp [NEG, *, b0, b1]

lemma NEG_of_ne {a b : range 2} (h : a ≠ b) : a = NEG b := by
  cases of_range_2B a
  case inl ha =>
    subst ha
    cases of_range_2B b
    case inl hb =>
      subst hb
      simp [NEG, b0, b1]
      simp at h
    case inr hb =>
     subst hb
     simp [NEG, b0, b1]
  case inr ha =>
    subst ha
    cases of_range_2B b
    case inr hb =>
      subst hb
      simp [NEG, b0, b1]
      simp at h
    case inl hb =>
     subst hb
     simp [NEG, b0, b1]

@[simp]
lemma NEG_NEG (a : range 2) : NEG (NEG a) = a := by
  cases of_range_2B a <;> simp [NEG, b0, b1, *]

def bit_to_bit_functions (f : range 2 → range 2) :
  f = C0 ∨ f = C1 ∨ f = ID ∨ f = NEG := by
  cases of_range_2B (f b0)
  case inl h0 =>
    cases of_range_2B (f b1)
    case inl h1 =>
      left
      funext b
      cases of_range_2B b
      case inl h => subst h; assumption
      case inr h => subst h; assumption
    case inr h1 =>
      right; right; left
      funext b
      cases of_range_2B b
      case inl h => subst h; assumption
      case inr h => subst h; assumption
  case inr h0 =>
    cases of_range_2B (f b1)
    case inl h1 =>
      right; right; right
      funext b
      cases of_range_2B b
      case inl h => subst h; assumption
      case inr h => subst h; assumption
    case inr h1 =>
      right; left
      funext b
      cases of_range_2B b
      case inl h => subst h; assumption
      case inr h => subst h; assumption

lemma bijective_ID : ID.Bijective := by
  exact Function.Involutive.bijective (congrFun rfl)

lemma bijective_NEG : NEG.Bijective := by
  constructor
  · intro a₁ a₂ h
    cases of_range_2B a₁
    case inl h₁ =>
      subst h₁
      cases of_range_2B a₂
      case inl h₂ => subst h₂; rfl
      case inr h₂ => subst h₂; simp [NEG, b0, b1] at h
    case inr h₁ =>
      subst h₁
      cases of_range_2B a₂
      case inr h₂ => subst h₂; rfl
      case inl h₂ => subst h₂; simp [NEG, b0, b1] at h
  · intro b
    cases of_range_2B b
    case inl h =>
      use b1
      simp [NEG, h]
    case inr h =>
      use b0
      simp [NEG, h]

lemma of_bijectiveB {f : range 2 → range 2} (hf : f.Bijective) :
  f = ID ∨ f = NEG := by
  cases of_range_2B (f b0)
  case inl h =>
    left
    funext b
    cases of_range_2B b
    case inl h' => simp [ID, h']; assumption
    case inr h' =>
      simp [ID, h']
      cases of_range_2B (f b1)
      case inr _ => assumption
      case inl h'' =>
        rw [←h] at h''
        have := hf.1 h''
        simp [b0, b1] at this
  case inr h =>
    right
    funext b
    cases of_range_2B b
    case inl h' => simp [NEG, h']; assumption
    case inr h' =>
      simp [NEG, h']
      cases of_range_2B (f b1)
      case inl _ => assumption
      case inr h'' =>
        rw [←h''] at h
        have := hf.1 h
        simp [b0, b1] at this

-- classification of Latin squares

def XOR (x : range 2 → range 2) : range 2 :=
  if x range_0 = x range_1 then
    b0
  else
    b1

def XNOR (x : range 2 → range 2) : range 2 :=
  if x range_0 = x range_1 then
    b1
  else
    b0

lemma is_XOR_of_is_Latin_square {f : (range 2 → range 2) → range 2}
  (hf : is_Latin_square f) : f = XOR ∨ f = XNOR := by
  cases of_range_2B (f (cons_input b0 b0))
  case inl h₀₀ =>
    have h₀₁ : f (cons_input b0 b1) = b1 := by
      cases of_range_2B (f (cons_input b0 b1))
      case inr => assumption
      case inl h₀₁ =>
        have := (hf.1 b0).1 (Eq.trans h₀₀ (Eq.symm h₀₁))
        simp [b0, b1] at this
    have h₁₀ : f (cons_input b1 b0) = b1 := by
      cases of_range_2B (f (cons_input b1 b0))
      case inr => assumption
      case inl h₁₀ =>
        have := (hf.2 b0).1 (Eq.trans h₀₀ (Eq.symm h₁₀))
        simp [b0, b1] at this
    have h₁₁ : f (cons_input b1 b1) = b0 := by
      cases of_range_2B (f (cons_input b1 b1))
      case inl => assumption
      case inr h₁₁ =>
        have := (hf.2 b1).1 (Eq.trans h₀₁ (Eq.symm h₁₁))
        simp [b0, b1] at this
    left
    funext x
    rw [←cons_input_of_components x]
    unfold XOR
    cases of_range_2B (x range_0)
    case inl h0 =>
      cases of_range_2B (x range_1)
      case inl h1 => simp [h0, h1, cons_input]; assumption
      case inr h1 => simp [h0, h1, cons_input]; assumption
    case inr h0 =>
      cases of_range_2B (x range_1)
      case inl h1 => simp [h0, h1, cons_input]; assumption
      case inr h1 => simp [h0, h1, cons_input]; assumption
  case inr h₀₀ =>
    have h₀₁ : f (cons_input b0 b1) = b0 := by
      cases of_range_2B (f (cons_input b0 b1))
      case inl => assumption
      case inr h₀₁ =>
        have := (hf.1 b0).1 (Eq.trans h₀₀ (Eq.symm h₀₁))
        simp [b0, b1] at this
    have h₁₀ : f (cons_input b1 b0) = b0 := by
      cases of_range_2B (f (cons_input b1 b0))
      case inl => assumption
      case inr h₁₀ =>
        have := (hf.2 b0).1 (Eq.trans h₀₀ (Eq.symm h₁₀))
        simp [b0, b1] at this
    have h₁₁ : f (cons_input b1 b1) = b1 := by
      cases of_range_2B (f (cons_input b1 b1))
      case inr => assumption
      case inl h₁₁ =>
        have := (hf.2 b1).1 (Eq.trans h₀₁ (Eq.symm h₁₁))
        simp [b0, b1] at this
    right
    funext x
    rw [←cons_input_of_components x]
    unfold XNOR
    cases of_range_2B (x range_0)
    case inl h0 =>
      cases of_range_2B (x range_1)
      case inl h1 => simp [h0, h1, cons_input]; assumption
      case inr h1 => simp [h0, h1, cons_input]; assumption
    case inr h0 =>
      cases of_range_2B (x range_1)
      case inl h1 => simp [h0, h1, cons_input]; assumption
      case inr h1 => simp [h0, h1, cons_input]; assumption

-- simplification of n = 1 check

def iterate_polyB {pred} (poly : Polymorphism₁B pred) (n : ℕ) : Polymorphism₁B pred :=
{
  fs i σ := (poly.fs i)^[n] σ,
  app y Py := by
    induction n
    case zero =>
      simp
      exact Py
    case succ n' hn' =>
      have := poly.app _ hn'
      conv at this =>
        congr
        ext i
        rw [←Function.iterate_succ_apply' (poly.fs i) _ _]
      assumption
}

def is_monotone_counterexample {pred : PredicateB}
  (poly : Polymorphism₁B pred) :=
    (∀ i, poly.fs i = C0 ∨ poly.fs i = C1 ∨ poly.fs i = ID) ∧
    (∃ i, poly.fs i = C0 ∨ poly.fs i = C1) ∧
    (∃ y, ¬ pred.P y ∧
      (∀ i, poly.fs i = C0 → y i = b0) ∧
      (∀ i, poly.fs i = C1 → y i = b1))

def has_monotone_counterexample (pred : PredicateB) :=
  ∃ poly : Polymorphism₁B pred, is_monotone_counterexample poly

def is_nonconst_counterexample {pred : PredicateB} (Φ : Set (formatB pred))
  (poly : Polymorphism₁B pred) :=
  (∀ i, poly.fs i = ID ∨ poly.fs i = NEG) ∧ poly.fs ∉ Φ

def has_nonconst_counterexample {pred : PredicateB} (Φ : Set (formatB pred)) :=
  ∃ poly : Polymorphism₁B pred, is_nonconst_counterexample Φ poly

theorem not_trivial_for_1B {pred Φ}
  (hnontrivial : ¬ trivial_for₁B pred Φ) :
  has_monotone_counterexample pred ∨
  has_nonconst_counterexample Φ := by
  unfold trivial_for₁B at hnontrivial
  push_neg at hnontrivial
  obtain ⟨poly, hndict, hncert⟩ := hnontrivial
  by_cases ∃ i, poly.fs i = C0 ∨ poly.fs i = C1
  case pos h =>
    left
    obtain ⟨i, hi⟩ := h
    let poly2 := iterate_polyB poly 2
    use iterate_polyB poly 2
    have hC0 {i} (h : poly.fs i = C0) : poly2.fs i = C0 := by
      unfold poly2 iterate_polyB C0
      ext σ
      simp
      rw [h]
      simp [C0]
    have hC1 {i} (h : poly.fs i = C1) : poly2.fs i = C1 := by
      unfold poly2 iterate_polyB C1
      ext σ
      simp
      rw [h]
      simp [C1]
    have hID {i} (h : poly.fs i = ID) : poly2.fs i = ID := by
      unfold poly2 iterate_polyB ID
      ext σ
      simp
      rw [h]
      simp [ID]
    have hNEG {i} (h : poly.fs i = NEG) : poly2.fs i = ID := by
      unfold poly2 iterate_polyB ID
      ext σ
      simp
      rw [h]
      simp [NEG]
      cases of_range_2B σ
      case inl h =>
        subst h
        simp [b0, b1]
      case inr h =>
        subst h
        simp [b0, b1]
    have hC0' {i} (h : poly2.fs i = C0) : poly.fs i = C0 := by
      cases bit_to_bit_functions (poly.fs i)
      case inl h' => assumption
      case inr h' =>
      cases h'
      case inl h' => rw [hC1 h'] at h; contradiction
      case inr h' =>
      cases h'
      case inl h' => rw [hID h'] at h; contradiction
      case inr h' => rw [hNEG h'] at h; contradiction
    have hC1' {i} (h : poly2.fs i = C1) : poly.fs i = C1 := by
      cases bit_to_bit_functions (poly.fs i)
      case inl h' => rw [hC0 h'] at h; contradiction
      case inr h' =>
      cases h'
      case inl h' => assumption
      case inr h' =>
      cases h'
      case inl h' => rw [hID h'] at h; contradiction
      case inr h' => rw [hNEG h'] at h; contradiction
    constructor
    · intro i
      cases bit_to_bit_functions (poly.fs i)
      case inl h => left; exact hC0 h
      case inr h =>
      cases h
      case inl h => right; left; exact hC1 h
      case inr h =>
      cases h
      case inl h => right; right; exact hID h
      case inr h => right; right; exact hNEG h
    constructor
    · use i
      cases hi
      case inl h => left; exact hC0 h
      case inr h => right; exact hC1 h
    · contrapose! hncert
      let c : CertificateB pred :=
      {
        dom := {i | poly.fs i = C0 ∨ poly.fs i = C1},
        ρ i := if poly.fs i = C0 then b0 else b1,
        cert x hx := by
          replace hncert := hncert x
          contrapose! hncert
          constructor
          · assumption
          constructor
          · intro i hi
            replace hi := hC0' hi
            have hi' : poly.fs i = C0 ∨ poly.fs i = C1 := by left; exact hi
            have := hx ⟨i, hi'⟩
            simp [hi] at this
            assumption
          · intro i hi
            replace hi := hC1' hi
            have hi' : poly.fs i = C0 ∨ poly.fs i = C1 := by right; exact hi
            have := hx ⟨i, hi'⟩
            simp [hi] at this
            assumption
      }
      use c
      intro i
      simp [c]
      simp [c] at i
      cases i.2
      case inl h => simp [h]; rfl
      case inr h => simp [h]; rfl
  case neg h =>
    right
    push_neg at h
    use poly
    constructor
    · intro i
      have hi := h i
      have := bit_to_bit_functions (poly.fs i)
      simp [hi] at this
      exact this
    · assumption
