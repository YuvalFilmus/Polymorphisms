import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

def AND {n} (J : Finset (range n)) (b : range 2) (x : range n → range 2) : range 2 :=
  if ∀ j ∈ J, x j = b then b else NEG b

def CONST {n} (b : range 2) (_ : range n → range 2) : range 2 := b

lemma parity_polymorphisms_if_AND {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (J : Finset (range n)) :
  ∃ poly : PolymorphismB P n, ∀ i, poly.fs i = AND J b := by
  sorry

lemma parity_polymorphisms_if_cert {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} {fs : range P.m → (range n → range 2) → range 2}
  {I : Finset (range P.m)} (sI : #I = m - w) (hI : ∀ i ∈ I, fs i = CONST (NEG b)) :
  ∃ poly : PolymorphismB P n, poly.fs = fs := by
  sorry

lemma parity_polymorphisms_only_if {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (poly : PolymorphismB P n) :
  (∃ (J : Finset (range n)), ∀ i, poly.fs i = AND J b) ∨
  (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, poly.fs i = CONST (NEG b)) := by
  sorry

lemma parity_polymorphisms {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  (∃ (J : Finset (range n)), ∀ i, fs i = AND J b) ∨
  (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, fs i = CONST (NEG b))
  := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    convert parity_polymorphisms_only_if h poly
    repeat exact hpoly.symm
  case mpr =>
    rintro h
    cases h
    case inl h =>
      obtain ⟨J, hJ⟩ := h
      obtain ⟨poly, hpoly⟩ := parity_polymorphisms_if_AND h J
      use poly
      funext i
      rw [hJ i, hpoly i]
    case inr h =>
      obtain ⟨I, sI, hI⟩ := h
      apply parity_polymorphisms_if_cert h sI hI

end NontrivialType
