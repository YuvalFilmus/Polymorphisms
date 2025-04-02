-- in this file we classify all polymorphisms of symmetric Boolean predicates in the trivial cases

import Polymorphisms.Symmetric
open Finset

lemma symmetric_polymorphisms_only_if_dict {S : SymmetricB}
  {n} (fs : range S.m → (range n → range 2) → range 2)
  (hfs : ∃ j, ∀ i x, fs i x = x j) :
  (∃ poly : PolymorphismB (P_of_S S) n, poly.fs = fs) := by
  obtain ⟨j, hfs⟩ := hfs
  use {
    fs := fs
    app xs sat := by
      conv =>
        arg 2
        ext i
        rw [hfs i]
      exact sat j
  }

lemma symmetric_polymorphisms_only_if_cert {S : SymmetricB}
  {n} (fs : range S.m → (range n → range 2) → range 2)
  (hfs : ∃ c : CertificateB (P_of_S S), ∀ (i : c.dom) x, fs i.1 x = c.ρ i) :
  (∃ poly : PolymorphismB (P_of_S S) n, poly.fs = fs) := by
  obtain ⟨c, hfs⟩ := hfs
  use {
    fs := fs
    app xs sat := by
      apply c.cert
      intro i
      simp [hfs i]
  }

lemma symmetric_polymorphisms_only_if_comp_closed {S : SymmetricB} (hcomp : is_comp_closed S)
  {n} (fs : range S.m → (range n → range 2) → range 2)
  (hfs : ∃ j, ∀ i x, fs i x = NEG (x j)) :
  (∃ poly : PolymorphismB (P_of_S S) n, poly.fs = fs) := by
  obtain ⟨j, hfs⟩ := hfs
  use {
    fs := fs
    app xs sat := by
      conv =>
        arg 2
        ext i
        rw [hfs i]
      have := NEG_vec_of_comp_closed hcomp (sat j)
      simp [NEG_vec] at this
      exact this
  }

lemma symmetric_polymorphisms_if {S : SymmetricB} (hS : ¬ is_nontrivial_S S)
  {n} (poly : PolymorphismB (P_of_S S) n) :
  ((∃ j, ∀ i x, poly.fs i x = x j) ∨
    (is_comp_closed S ∧ (∃ j, ∀ i x, poly.fs i x = NEG (x j))) ∨
    ∃ c : CertificateB (P_of_S S), ∀ (i : c.dom) x, poly.fs i.1 x = c.ρ i) := by
  have htrivial : ∀ n, trivial_forB (P_of_S S) (Φ_std .neg S) n := by
    apply (symmetric_classification .neg S).mpr
    constructor
    exact hS
    tauto
  cases htrivial n poly
  case inl hdict =>
    obtain ⟨j, φ, φ_in_Φ, hfs⟩ := hdict
    by_cases ∀ i, φ i = ID
    case pos hID =>
      left
      use j
      intro i x
      rw [hfs i x, hID i, ID]
    case neg hnontrivial =>
      let e : Polymorphism₁B (P_of_S S) := {
        fs i := φ i
        app x Px := by
          let xs (i : range S.m) (_ : range n) := x i
          have sat (j : range n) : (P_of_S S).P (xs · j) := by
            simp [xs]
            exact Px
          convert poly.app xs sat with i
          simp [xs, hfs i]
      }
      have hnonconst i : e.fs i = ID ∨ e.fs i = NEG := by
        simp [Φ_std, Φ_neg] at φ_in_Φ
        exact φ_in_Φ i.1 (mem_range.mp i.2)
      replace hnontrivial : ∃ i, e.fs i = NEG := by
        push_neg at hnontrivial
        obtain ⟨i, hi⟩ := hnontrivial
        use i
        simp [e]
        have := hnonconst i
        simp [e] at this
        tauto
      cases nontrivial_if_has_nonconst_counterexample' hnonconst hnontrivial
      case inl hnontrivial => contradiction
      case inr hNEG =>
        obtain ⟨hcomp, hNEG⟩ := hNEG
        right; left
        constructor
        exact hcomp
        use j
        intro i x
        rw [hfs i x]
        simp only [e] at hNEG
        rw [hNEG i]
  case inr hcert =>
    right; right
    obtain ⟨c, hc⟩ := hcert
    use c

theorem symmetric_polymorphisms_not_comp_closed
  {S : SymmetricB} (hS : ¬ is_nontrivial_S S) (hcomp : ¬ is_comp_closed S)
  {n} (fs : range S.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB (P_of_S S) n, poly.fs = fs) ↔
  ((∃ j, ∀ i x, fs i x = x j) ∨
    ∃ c : CertificateB (P_of_S S), ∀ (i : c.dom) x, fs i.1 x = c.ρ i) := by
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    cases symmetric_polymorphisms_if hS poly
    case inl hdict_id => left; rw [←hpoly]; exact hdict_id
    case inr h =>
    cases h
    case inl hdict_neg =>
      exfalso
      exact hcomp hdict_neg.1
    case inr hcert => right; rw [←hpoly]; exact hcert
  case mpr =>
    intro h
    cases h
    case inl hdict => exact symmetric_polymorphisms_only_if_dict fs hdict
    case inr hcert => exact symmetric_polymorphisms_only_if_cert fs hcert

theorem symmetric_polymorphisms_comp_closed
  {S : SymmetricB} (hS : ¬ is_nontrivial_S S) (hcomp : is_comp_closed S)
  {n} (fs : range S.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB (P_of_S S) n, poly.fs = fs) ↔
  (∃ j, ∀ i x, fs i x = x j) ∨ (∃ j, ∀ i x, fs i x = NEG (x j)) ∨
    ∃ c : CertificateB (P_of_S S), ∀ (i : c.dom) x, fs i.1 x = c.ρ i := by
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    cases symmetric_polymorphisms_if hS poly
    case inl hdict_id => left; rw [←hpoly]; exact hdict_id
    case inr h =>
    cases h
    case inl hdict_neg => right; left; rw [←hpoly]; exact hdict_neg.2
    case inr hcert => right; right; rw [←hpoly]; exact hcert
  case mpr =>
    intro h
    cases h
    case inl hdict_id => exact symmetric_polymorphisms_only_if_dict fs hdict_id
    case inr h =>
    cases h
    case inl hdict_neg => exact symmetric_polymorphisms_only_if_comp_closed hcomp fs hdict_neg
    case inr hcert => exact symmetric_polymorphisms_only_if_cert fs hcert
