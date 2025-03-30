import Polymorphisms.SymmetricClassify
open Finset

namespace Nat.ModEq

-- is this really not in Mathlib?
lemma sum {α} [DecidableEq α] {s : Finset α} {f g : α → ℕ} {m} (h : ∀ x ∈ s, f x ≡ g x [MOD m]) :
  ∑ x ∈ s, f x ≡ ∑ x ∈ s, g x [MOD m] := by
  induction s using Finset.induction
  case empty =>
    simp
    rfl
  case insert a y ha hind =>
    rw [sum_insert ha, sum_insert ha]
    apply Nat.ModEq.add
    · apply h
      simp
    · apply hind
      intro x hx
      apply h
      apply mem_insert_of_mem
      exact hx

end Nat.ModEq

namespace NontrivialType

def XOR {n} (J : Finset (range n)) (b : range 2) (x : range n → range 2) : range 2 := by
  use (∑ j ∈ J, (x j).val + b.val) % 2
  apply mem_range.mpr
  omega

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

lemma parity_polymorphisms_if {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  (n : ℕ) (J : Finset (range n)) (b : range P.m → range 2)
  (hb : ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2]) :
  ∃ poly : PolymorphismB P n, poly.fs = fun i ↦ XOR J (b i) := by
  obtain ⟨Pm, PP⟩ := parity_def h
  symm at Pm
  subst Pm
  use {
    fs i := XOR J (b i),
    app xs sat := by
      apply (PP _).mpr
      simp [wt_alt, XOR]
      calc
        ∑ i : range P.m, (∑ j ∈ J, ↑(xs i j) + ↑(b i)) % 2
        ≡ ∑ i : range P.m, (∑ j ∈ J, ↑(xs i j) + ↑(b i)) [MOD 2] := by
          simp [Nat.ModEq]
          rw [← @sum_nat_mod]
        _ ≡ ∑ i : range P.m, ∑ j ∈ J, ↑(xs i j) + ∑ i : range P.m, ↑(b i) [MOD 2] := by
          rw [sum_add_distrib]
        _ ≡ ∑ i : range P.m, ∑ j ∈ J, ↑(xs i j) + (#J + 1) * p [MOD 2] := by
          apply Nat.ModEq.add_left
          assumption
        _ ≡ ∑ j ∈ J, ∑ i : range P.m, ↑(xs i j) + (#J + 1) * p [MOD 2] := by
          rw [sum_comm]
        _ ≡ ∑ j ∈ J, ↑p + (#J + 1) * p [MOD 2] := by
          apply Nat.ModEq.add_right
          apply Nat.ModEq.sum
          intro i hi
          rw [← wt_alt]
          apply (PP _).mp
          apply sat i
        _ ≡ #J * p + (#J + 1) * p [MOD 2] := by
          congr
          apply sum_const
        _ ≡ 2 * #J * p + p [MOD 2] := by
          congr 1
          ring
        _ ≡ 0 + p [MOD 2] := by
          apply Nat.ModEq.add_right
          apply Nat.modEq_zero_iff_dvd.mpr
          rw [mul_assoc]
          apply Nat.dvd_mul_right
        _ ≡ p [MOD 2] := by
          congr
          apply zero_add
  }

lemma parity_polymorphisms_only_if {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  {n} (poly : PolymorphismB P n) :
  ∃ J, ∃ (b : range P.m → range 2),
    ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range P.m), poly.fs i = XOR J (b i) := by
  sorry

lemma parity_polymorphisms {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  ∃ J, ∃ (b : range P.m → range 2),
    ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range P.m), fs i = XOR J (b i)
  := by
  obtain ⟨Pm, PP⟩ := parity_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    obtain ⟨J, b, hb, hfs⟩ := parity_polymorphisms_only_if h poly
    use J, b
    constructor
    exact hb
    convert hfs with i
    exact hpoly.symm
  case mpr =>
    rintro ⟨J, b, hb, hfs⟩
    convert parity_polymorphisms_if h n J b hb with poly i
    exact hfs i

end NontrivialType
