import Polymorphisms.SymmetricClassify
import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

lemma atmost_polymorphisms {P m w b hm hw} (h : P = P_of_S (atmost m w b hm hw).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  ∀ (xs : range P.m → (range n → range 2)) (I : Finset (range P.m)), #I = w+1 →
    (∀ i ∈ I, fs i (xs i) = b) → ∃ j, ∀ i ∈ I, xs i j = b
  := by
  obtain ⟨Pm, PP⟩ := atmost_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    symm at hpoly
    subst hpoly
    intro xs I hI hfs
    by_contra! hxs
    let ys (i : range P.m) (j : range n) : range 2 :=
      if i ∈ I then xs i j else NEG b
    have hys j : P.P (fun i ↦ ys i j) := by
      apply (PP _).mpr
      intro J hJ
      by_cases J = I
      case pos hJI =>
        subst hJI
        obtain ⟨i, hiJ, hi⟩ := hxs j
        apply @card_ne_zero_of_mem _ _ ⟨i, hiJ⟩ ?_
        simpa [ys]
      case neg hJI =>
        have : ∃ i ∈ J, i ∉ I := by
          by_contra! h
          have : J ⊆ I := h
          apply hJI
          apply eq_of_subset_of_card_le h
          rw [hI, hJ]
        obtain ⟨i, hiJ, hi⟩ := this
        apply @card_ne_zero_of_mem _ _ ⟨i, hiJ⟩ ?_
        simp [ys, hi]
        exact (ReductionTo1.neg₂_dichotomy rfl).mpr rfl
    apply (PP _).mp (poly.app ys hys) I hI
    apply card_filter_eq_zero_iff.mpr
    intro i _
    simp [ys]
    apply hfs i
    exact i.property
  case mpr =>
    intro h
    use {
      fs := fs,
      app := by
        intro xs sat
        replace sat j := (PP _).mp (sat j)
        apply (PP _).mpr
        intro I hI
        replace h := h xs I hI
        replace sat j := sat j I hI
        by_contra! h'
        replace h' := eq_empty_iff_forall_not_mem.mp (card_eq_zero.mp h')
        have : ∀ i ∈ I, fs i (xs i) = b := by
          intro i hi
          have := h' ⟨i, hi⟩
          simp at this
          assumption
        obtain ⟨j, hj⟩ := h this
        apply sat j
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_not_mem.mpr
        intro i
        simp
        apply hj
        exact i.property
    }

end NontrivialType
