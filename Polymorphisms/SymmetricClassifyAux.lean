import Polymorphisms.Basic
import Polymorphisms.Symmetric
open Finset

def other_ix {m} (hm : m ≥ 3) (i₀ i₁ : range m) : range m :=
  have : AtLeast3 m := ⟨hm⟩
  if i₀ ≠ range_0 ∧ i₁ ≠ range_0 then
    range_0
  else if i₀ ≠ range_1 ∧ i₁ ≠ range_1 then
    range_1
  else
    range_2

lemma other_ix_spec {m} (hm : m ≥ 3) (i₀ i₁ : range m) :
  other_ix hm i₀ i₁ ≠ i₀ ∧ other_ix hm i₀ i₁ ≠ i₁ := by
  simp [other_ix, range_0, range_1, range_2]
  split
  case isTrue h =>
    tauto
  case isFalse h =>
    split
    case isTrue h' =>
      tauto
    case isFalse h' =>
      constructor
      · by_contra! h''
        symm at h''
        subst h''
        simp at h
        simp at h'
        simp [h] at h'
      · by_contra! h''
        symm at h''
        subst h''
        simp at h
        simp at h'
        simp [h] at h'

def wt_alt {m} (x : range m → range 2) :
  (wt x).val = ∑ j : range m, (x j).val := by
  simp [wt]
  let e : range m ↪ ℕ := {
    toFun i := i.val,
    inj' := by simp
  }
  convert sum_map (range m).attach e (coe_vec x ·) with _ _ i hi
  · ext i
    constructor
    · intro hi
      apply mem_map.mpr
      use ⟨i, hi⟩
      simp [e]
    · intro hi
      simp [e] at hi
      apply mem_range.mpr
      assumption
  · simp [coe_vec, e, mem_range.mp i.property]
