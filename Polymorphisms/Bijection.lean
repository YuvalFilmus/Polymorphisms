-- lemmas about bijections

import Polymorphisms.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic
open Finset

def iterate_poly {pred} (poly : Polymorphism₁ pred) (n : ℕ) : Polymorphism₁ pred :=
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

instance (a : ℕ) [h : AtLeast1 a] : Nonempty (range a) := by
  use (range_0 : range a)
  simp

noncomputable def of_bijective {a : ℕ} [AtLeast1 a]
  {f : range a → range a} (hf : f.Bijective) :
  Equiv.Perm (range a) :=
{
  toFun := f,
  invFun := f.invFun,
  left_inv := Function.leftInverse_invFun hf.1
  right_inv := Function.rightInverse_invFun hf.2
}

lemma lagrange_bijective {a : ℕ} [AtLeast1 a] {f : range a → range a} (hf : f.Bijective)
  {n : ℕ} (hn : a.factorial ∣ n) :
  f^[n] = id := by
  let f' := of_bijective hf
  have hf' : of_bijective hf = f' := rfl
  have : f'^a.factorial = 1 := by
    convert pow_card_eq_one
    have := @Fintype.card_perm (range a) _ _
    simp at this
    rw [this]
  have pow_n : f'^n = 1 := by
    obtain ⟨m, hm⟩ := dvd_def.mp hn
    rw [hm]
    rw [pow_mul f' a.factorial m]
    rw [this]
    apply one_pow
  have := Equiv.Perm.coe_pow f' n
  rw [pow_n] at this
  symm
  convert this

noncomputable def inverse_poly {pred} (poly : Polymorphism₁ pred)
  (hfs : ∀ i, (poly.fs i).Bijective)
  : Polymorphism₁ pred :=
{
  fs i := (poly.fs i).invFun,
  app y Py := by
    let as := image pred.a univ
    have as_nonempty : as.Nonempty := by
      use pred.a range_0
      simp [as]
    let max_a := max' as as_nonempty
    let n := max_a.factorial - 1
    have hn : n.succ = max_a.factorial := by
      apply Nat.sub_one_add_one_eq_of_pos
      apply Nat.factorial_pos
    let q := iterate_poly poly n
    convert q.app y Py with _ i
    apply Function.invFun_eq_of_injective_of_rightInverse
    · exact (hfs i).1
    simp only [Function.RightInverse, Function.LeftInverse]
    suffices poly.fs i ∘ (q.fs i) = id by
      apply congr_fun this
    simp [q, iterate_poly]
    rw [←Function.iterate_succ' (poly.fs i) n, hn]
    apply lagrange_bijective
    · exact hfs i
    apply Nat.factorial_dvd_factorial
    apply le_max'
    simp [as]
}
