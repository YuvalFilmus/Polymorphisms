-- polymorphisms of NAE (includes Arrow's theorem for three candidates as a special case)

import Polymorphisms.SymmetricClassifyTrivialA
open Finset

def NAE {m : ℕ} (hm : m ≥ 3) : SymmetricB := {
  m := m
  W := {w | w.1 ≠ 0 ∧ w.1 ≠ m}
  notall0 := by
    use ⟨1, by in_range⟩
    simp
    omega
  notall1 := by
    use ⟨1, by in_range⟩
    simp
    omega
  notfull := by
    use ⟨0, by in_range⟩
    simp
}

lemma NAE_not_nontrivial {m : ℕ} (hm : m ≥ 3) :
  ¬ is_nontrivial_S (NAE hm) := by
  by_contra! h
  cases h
  -- rule out S_even
  case inl heven =>
    obtain ⟨m', hm', hS⟩ := heven
    simp [NAE, S_even] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨0, by in_range⟩
    simp at hS
  -- rule out S_odd
  case inr h =>
  cases h
  case inl hodd =>
    obtain ⟨m', hm', hS⟩ := hodd
    simp [NAE, S_odd] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨2, by in_range⟩
    simp [Odd] at hS
    omega
  -- rule out S_atmost
  case inr h =>
  cases h
  case inl hatmost =>
    obtain ⟨m, b, hlb, hub, hS⟩ := hatmost
    simp [NAE, S_atmost] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨0, by in_range⟩
    simp at hS
  -- rule out S_atleast
  case inr h =>
  cases h
  case inl hatleast =>
    obtain ⟨m, b, hlb, hub, hS⟩ := hatleast
    simp [NAE, S_atleast] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨m, by in_range⟩
    simp at hS
    omega
  -- rule out S_atmost_m
  case inr h =>
  cases h
  case inl hatmost_m =>
    obtain ⟨m, b, hub, hS⟩ := hatmost_m
    simp [NAE, S_atmost_m] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨m, by in_range⟩
    simp at hS
  -- rule out S_atleast_0
  case inr hatleast_0 =>
    obtain ⟨m, b, hlb, hub, hS⟩ := hatleast_0
    simp [NAE, S_atleast_0] at hS
    obtain ⟨hmm', hS⟩ := hS
    subst hmm'
    simp at hS
    replace hS := Finset.ext_iff.mp hS ⟨0, by in_range⟩
    simp at hS

lemma NAE_comp_closed {m : ℕ} (hm : m ≥ 3) : is_comp_closed (NAE hm) := by
  apply comp_closed
  intro w
  have := mem_range.mp w.property
  simp [NAE] at this
  simp [NAE, comp]
  intro h0 hm
  constructor
  contrapose! hm; omega
  contrapose! h0; omega

lemma NAE_cert {m : ℕ} (hm : m ≥ 3)
  (c : CertificateB (P_of_S (NAE hm))) :
  ∃ i₀ i₁, c.ρ i₀ = b0 ∧ c.ρ i₁ = b1 := by
  by_contra! hcontra
  by_cases ∃ i₀, c.ρ i₀ = b0
  case pos h =>
    obtain ⟨i₀, hi₀⟩ := h
    let x (i : range m) := b0
    have hx (i : c.dom) : x i.1 = c.ρ i := by
      cases of_range_2B (c.ρ i)
      case inl h => rw [h]
      case inr h => have := hcontra i₀ i hi₀; contradiction
    have Px := c.cert x hx
    have wt_x : wt x = ⟨0, by in_range⟩ := by apply wt_0.mpr; simp [x]
    have wt_x_in_W := P_iff_wt.mp Px
    rw [wt_x] at wt_x_in_W
    simp [NAE] at wt_x_in_W
  case neg h =>
    push_neg at h
    let x (i : range m) := b1
    have hx (i : c.dom) : x i.1 = c.ρ i := by
      cases of_range_2B (c.ρ i)
      case inr h' => rw [h']
      case inl h' => have := h i; contradiction
    have Px := c.cert x hx
    have wt_x : wt x = ⟨m, by in_range⟩ := by apply wt_m.mpr; simp [x]
    have wt_x_in_W := P_iff_wt.mp Px
    rw [wt_x] at wt_x_in_W
    simp [NAE] at wt_x_in_W

theorem NAE_polymorphisms {m : ℕ} (hm : m ≥ 3)
  {n} (fs : range m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB (P_of_S (NAE hm)) n, poly.fs = fs) ↔
  (∃ j, ∀ i x, fs i x = x j) ∨
  (∃ j, ∀ i x, fs i x = NEG (x j)) ∨
  (∃ i₀ i₁, ∀ x, fs i₀ x = b0 ∧ fs i₁ x = b1) := by
  convert symmetric_polymorphisms_comp_closed
    (NAE_not_nontrivial hm) (NAE_comp_closed hm) fs
  constructor
  case mp =>
    rintro ⟨i₀, i₁, hfs⟩
    have hdiff : i₀ ≠ i₁ := by
      by_contra! h
      subst h
      obtain ⟨h₀, h₁⟩ := hfs (fun _ ↦ b0)
      rw [h₀] at h₁
      simp [b0, b1] at h₁
    use {
      dom := {i₀, i₁}
      ρ i := if i.1 = i₀ then b0 else b1
      cert x hx := by
        apply P_iff_wt.mpr
        simp [NAE]
        constructor
        · by_contra! h
          have h₀ := wt_0.mp (Subtype.coe_eq_of_eq_mk h) i₁
          have h₁ := hx ⟨i₁, by simp⟩
          symm at hdiff
          simp [hdiff] at h₁
          rw [h₀] at h₁
          simp [b0, b1] at h₁
        · by_contra! h
          have h₀ := wt_m.mp (Subtype.coe_eq_of_eq_mk h) i₀
          have h₁ := hx ⟨i₀, by simp⟩
          symm at hdiff
          simp [hdiff] at h₁
          rw [h₀] at h₁
          simp [b0, b1] at h₁
    }
    intro i x
    have hi := i.property
    dsimp at hi
    have : i.1 = i₀ ∨ i.1 = i₁ := by aesop
    cases this
    case inl hi₀ =>
      rw [hi₀]
      simp [hi₀]
      exact (hfs x).1
    case inr hi₁ =>
      rw [hi₁]
      symm at hdiff
      simp [hi₁, hdiff]
      exact (hfs x).2
  case mpr =>
    rintro ⟨c, hc⟩
    obtain ⟨i₀, i₁, hfs⟩ := NAE_cert hm c
    use i₀.1, i₁.1
    intro x
    constructor
    · rw [hc i₀, hfs.1]
    · rw [hc i₁, hfs.2]
