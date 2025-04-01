import Polymorphisms.SymmetricClassifyAtmost_mIf
import Polymorphisms.SymmetricClassifyAtmost_mOnlyIf
open Finset

namespace NontrivialType

lemma atmost_m_polymorphisms {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  (∃ (J : Finset (range n)), ∀ i, fs i = AND' J b) ∨
  (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, fs i = CONST (NEG b))
  := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    convert atmost_m_polymorphisms_only_if h poly
    repeat exact hpoly.symm
  case mpr =>
    rintro h
    cases h
    case inl h =>
      obtain ⟨J, hJ⟩ := h
      obtain ⟨poly, hpoly⟩ := atmost_m_polymorphisms_if_AND' h J
      use poly
      funext i
      rw [hJ i, hpoly i]
    case inr h =>
      obtain ⟨I, sI, hI⟩ := h
      apply atmost_m_polymorphisms_if_cert h sI hI

end NontrivialType
