-- classify a Boolean polymorphism into types

import Polymorphisms.Boolean
import Polymorphisms.SymmetricDefs
open Finset

inductive NontrivialType where
  | odd2
  | equal (m : ℕ) (hm : m ≥ 2)
  | parity (m : ℕ) (p : range 2) (hm : m ≥ 3)
  | atmost (m w : ℕ) (b : range 2) (hm : m ≥ w + 1) (hw : w ≥ 1)
  | atmost_m (m w : ℕ) (b : range 2) (hm : m ≥ w + 2) (hw : w ≥ 1)

namespace NontrivialType

-- denotation of BooleanType other than other
def denotation
| odd2 => @S_odd 2 (by omega)
| equal m hm => @S_atmost_m m 0 (by omega)
| parity m p hm =>
  if p.val = 0 then
    @S_even m (by omega)
  else
    @S_odd m (by omega)
| atmost m w b hm hw =>
  if b.val = 1 then
    @S_atmost m w (by omega) (by omega)
  else
    @S_atleast m (m-w) (by omega) (by omega)
| atmost_m m w b hm hw =>
  if b.val = 1 then
    @S_atmost_m m w (by omega)
  else
    @S_atleast_0 m (m-w) (by omega) (by omega)

lemma nontrivial_denotation (S : SymmetricB)
  (hS : is_nontrivial_S S) :
  ∃ nt, denotation nt = S := by
  rcases hS with
    ⟨m, hm, hS, _⟩ |
    ⟨m, hm, hS, _⟩ |
    ⟨m, b, hlb, hub, hS, _⟩ |
    ⟨m, b, hlb, hub, hS, _⟩ |
    ⟨m, b, hub, hS, _⟩ |
    ⟨m, b, hlb, hub, hS, _⟩
  · by_cases m ≥ 3
    case pos hm' =>
      use parity m b0 hm'
      simp [b0, denotation, S_even]
    case neg hm' =>
      use equal m hm
      have : m = 2 := by omega
      subst this
      simp [denotation, S_atmost_m, S_even]
      aesop
  · by_cases m ≥ 3
    case pos hm' =>
      use parity m b1 hm'
      simp [b1, denotation, S_odd]
    case neg hm' =>
      use odd2
      have : m = 2 := by omega
      subst this
      simp [denotation]
  · use atmost m b b1 (by omega) (by omega)
    simp [denotation, b1]
  · use atmost m (m-b) b0 (by omega) (by omega)
    simp [denotation, b0]
    congr
    omega
  · by_cases b ≥ 1
    case pos hb =>
      use atmost_m m b b1 (by omega) (by omega)
      simp [denotation, b1]
    case neg hb =>
      use equal m (by omega)
      have : b = 0 := by omega
      subst this
      simp [denotation, S_atmost_m]
  · by_cases b ≤ m-1
    case pos hb =>
      use atmost_m m (m-b) b0 (by omega) (by omega)
      simp [denotation, b0]
      congr
      omega
    case neg hb =>
      use equal m (by omega)
      have : b = m := by omega
      subst this
      simp [denotation, S_atleast_0, S_atmost_m]
      congr
      funext w
      have := mem_range.mp w.property
      have : b ≤ w ↔ w = b := by omega
      rw [this]
      aesop

instance (P : PredicateB) : AtLeast2 P.m := by
  refine { cond := ?_ }
  by_contra! h
  have : P.m ≥ 1 := P.hm
  replace h : P.m = 1 := by omega
  let r0 : range P.m := ⟨0, by apply mem_range.mpr; omega⟩
  obtain ⟨_, y, _, Py, _⟩ := P.dep r0
  apply Py
  obtain ⟨z, Pz, hz⟩ := P.full r0 (y r0)
  convert Pz
  funext i
  have : i.val = 0 := by
    have := mem_range.mp i.property
    omega
  aesop

lemma odd2_def {P} (h : P = P_of_S odd2.denotation) :
  P.m = 2 ∧
  ∀ x, P.P x ↔ x range_1 = NEG (x range_0)
  := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_odd]
  intro x
  have hwt : (wt x).val = x range_0 + x range_1 := by
    simp [wt, range, coe_vec, range_0, range_1]
    rw [add_comm]
  rw [hwt]
  cases of_range_2B (x range_0)
  case inl h0 =>
    cases of_range_2B (x range_1)
    case inl h1 => simp [h0, h1, NEG, b0, b1]
    case inr h1 => simp [h0, h1, NEG, b0, b1]
  case inr h0 =>
    cases of_range_2B (x range_1)
    case inl h1 => simp [h0, h1, NEG, b0, b1]
    case inr h1 => simp [h0, h1, NEG, b0, b1]

lemma equal_def {P m hm} (h : P = P_of_S (equal m hm).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ i, x i = x range_0
  := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_atmost_m]
  intro x
  constructor
  case mp =>
    intro h; cases h
    case inl h0 =>
      have : wt x = ⟨0, by apply mem_range.mpr; omega⟩ := by
        apply Subtype.eq
        assumption
      have := wt_0.mp this
      simp at this
      intro a ha
      simp [range_0]
      rw [this a ha, this 0 (by omega)]
    case inr hm =>
      have : wt x = ⟨m, by apply mem_range.mpr; omega⟩ := by
        apply Subtype.eq
        assumption
      have := wt_m.mp this
      simp at this
      intro a ha
      simp [range_0]
      rw [this a ha, this 0 (by omega)]
  case mpr =>
    intro h
    have : AtLeast1 m := ⟨by omega⟩
    cases of_range_2B (x range_0)
    case inl h0 =>
      left
      suffices wt x = ⟨0, by apply mem_range.mpr; omega⟩ by
        rw [this]
      apply wt_0.mpr
      simp
      intro a ha
      rw [h a ha, h0]
    case inr h1 =>
      right
      suffices wt x = ⟨m, by apply mem_range.mpr; omega⟩ by
        rw [this]
      apply wt_m.mpr
      simp
      intro a ha
      rw [h a ha, h1]

lemma parity_def {P m p hm} (h : P = P_of_S (parity m p hm).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ wt x ≡ p [MOD 2] := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_even, S_odd]
  cases of_range_2B p
  case inl hp =>
    subst hp
    simp [b0]
    intro x
    simp [Nat.ModEq]
    exact Nat.even_iff
  case inr hp =>
    subst hp
    simp [b1]
    intro x
    simp [Nat.ModEq]
    exact Nat.odd_iff

lemma atmost_def {P m w b hm hw} (h : P = P_of_S (atmost m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+1 → #{i : I | x i ≠ b} ≠ 0 := by
  sorry

lemma atmost_m_def {P m w b hm hw} (h : P = P_of_S (atmost m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+2 → #{i : I | x i ≠ b} ≠ 1 := by
  sorry

lemma odd2_polymorphisms {P} (h : P = P_of_S odd2.denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  ∀ x, fs range_1 x = NEG (fs range_0 (NEG_vec x)) := by
  obtain ⟨Pm, PP⟩ := odd2_def h
  constructor
  · rintro ⟨poly, hpoly⟩
    intro x
    let xs (i : range P.m) := if i.val = 0 then (NEG_vec x) else x
    have : ∀ j, P.P (fun i ↦ xs i j) := by
      intro j
      apply (PP _).mpr
      simp [xs, range_0, range_1, NEG_vec]
    convert (PP _).mp (poly.app xs this)
    exact hpoly.symm
    exact hpoly.symm
  · intro hfs
    use {
      fs := fs,
      app xs sat := by
        apply (PP _).mpr
        convert hfs _
        funext j
        simp [NEG_vec]
        convert sat j
        rw [PP _]
        aesop
    }

lemma equal_polymorphisms {P m hm} (h : P = P_of_S (equal m hm).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  ∀ i, fs i = fs (range_0) := by
  obtain ⟨Pm, PP⟩ := equal_def h
  constructor
  · rintro ⟨poly, hpoly⟩
    intro i
    funext x
    let xs (i : range P.m) := x
    have : ∀ j, P.P (fun i ↦ xs i j) := by
      intro j
      apply (PP _).mpr
      simp [xs]
    convert (PP _).mp (poly.app xs this) i
    exact hpoly.symm
    exact hpoly.symm
  · intro hfs
    use {
      fs := fs,
      app xs sat := by
        apply (PP _).mpr
        intro i
        rw [hfs i]
        congr
        funext j
        apply (PP _).mp (sat j)
    }

end NontrivialType
