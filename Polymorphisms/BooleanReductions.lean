-- in this file we prove specialized forms of the reductions in the Boolean setting

import Polymorphisms.Boolean
import Polymorphisms.ReductionTo2
import Polymorphisms.ReductionTo1
open Finset

theorem trivial_iff_trivial_for_2B (pred : PredicateB) (Φ : Set (formatB pred)) :
  (∀ n, trivial_forB pred Φ n) ↔ (trivial_forB pred Φ 2) := by
  constructor
  · intro hallB
    exact hallB 2
  · intro h2B n
    have h2 := trivial_for_of_trivial_forB h2B
    have hn := (trivial_iff_trivial_for_2 _ _).mpr h2 n
    convert trivial_forB_of_trivial_for (Predicate_of_PredicateB_boolean pred) hn
    simp

-- reduction to n = 1: definitions

section definitions

variable {pred : PredicateB}

def is_closed_underB (pred : PredicateB) (i : range pred.m) (σ : range 2) :=
  ∀ y, pred.P y → pred.P (set_coord_to i σ y)

def has_closureB (pred : PredicateB) :=
  ∃ i σ, is_closed_underB pred i σ

def AND (x : range 2 → range 2) : range 2 :=
  if x range_0 = b1 ∧ x range_1 = b1 then b1 else b0

def OR (x : range 2 → range 2) : range 2 :=
  if x range_0 = b0 ∧ x range_1 = b0 then b0 else b1

def is_AND_OR_polyB (poly : PolymorphismB pred 2) :=
  ∀ i, poly.fs i = AND ∨ poly.fs i = OR

def has_AND_OR_polyB (pred : PredicateB) :=
  ∃ poly : PolymorphismB pred 2, is_AND_OR_polyB poly

def is_Latin_square_polyB (Φ : Set (formatB pred)) (poly : PolymorphismB pred 2) :=
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input (y i) τ)) ∈ Φ) ∧
  (∀ y, pred.P y → (fun i τ => poly.fs i (cons_input τ (y i))) ∈ Φ)

def has_Latin_square_polyB (pred : PredicateB) (Φ : Set (formatB pred)) :=
  ∃ poly : PolymorphismB pred 2, is_Latin_square_polyB Φ poly

end definitions

theorem trivial_for_2_of_trivial_for_1B {pred : PredicateB} {Φ : Set (formatB pred)}
  (hperm : permutationalB Φ) (htrivial : trivial_for₁B pred Φ) :
  trivial_forB pred Φ 2 ∨
  has_closureB pred ∨
  has_AND_OR_polyB pred ∨
  has_Latin_square_polyB pred Φ := by
  let hpred := (Predicate_of_PredicateB_boolean pred)
  have hperm' : permutational (formats_of_formatsB Φ) := permutational_of_permutationalB hperm
  have := (trivial_for_1_iff_trivial_for₁B _ _).mpr htrivial
  have := trivial_for_of_trivial_forB this
  have := (trivial_for_1_iff_trivial_for₁ _ _).mp this
  cases trivial_for_2_of_trivial_for_1 hperm' this
  case inl h =>
    left
    convert trivial_forB_of_trivial_for hpred h
    simp
  case inr h =>
  right
  cases h
  case inl h =>
    left
    obtain ⟨i, σ, h⟩ := h
    use i, σ
    intro y Py
    convert h y Py
  case inr h =>
  right
  cases h
  case inl h =>
    left
    obtain ⟨_, poly, hpoly⟩ := h
    use PolymorphismB_of_Polymorphism hpred poly
    intro i
    cases hpoly.1 i (hpred i)
    case inl h =>
      left
      simp [PolymorphismB_of_Polymorphism, scalar_toB]
      rw [h]
      funext x
      simp [AND₂, vector_fromB']
      rfl
    case inr h =>
      right
      simp [PolymorphismB_of_Polymorphism, scalar_toB]
      rw [h]
      funext x
      simp [OR₂, vector_fromB']
      rfl
  case inr h =>
    right
    obtain ⟨poly, hpoly⟩ := h
    use PolymorphismB_of_Polymorphism hpred poly
    constructor
    · intro y Py
      have := hpoly.1 y Py
      simp [PolymorphismB_of_Polymorphism, scalar_toB]
      unfold formats_of_formatsB at this
      simp [format_of_formatB] at this
      obtain ⟨φ, hφ, hconv⟩ := this
      unfold format_of_formatB at hconv
      replace hconv := congrFun₂ hconv
      convert hφ with _ _ x i σ
      rw [hconv i σ]
      rfl
    · intro y Py
      have := hpoly.2 y Py
      simp [PolymorphismB_of_Polymorphism, scalar_toB]
      unfold formats_of_formatsB at this
      simp [format_of_formatB] at this
      obtain ⟨φ, hφ, hconv⟩ := this
      unfold format_of_formatB at hconv
      replace hconv := congrFun₂ hconv
      convert hφ with _ _ x i σ
      rw [hconv i σ]
      rfl

lemma is_Latin_square_of_is_Latin_square_polyB {pred : PredicateB}
  {Φ : Set (formatB pred)} (hperm : permutationalB Φ)
  {poly : PolymorphismB pred 2} (hLatin : is_Latin_square_polyB Φ poly)
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
