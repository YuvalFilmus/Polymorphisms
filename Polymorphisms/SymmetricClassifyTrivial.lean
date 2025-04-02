import Polymorphisms.SymmetricClassify
import Polymorphisms.SymmetricClassifyTrivialA
open Finset

namespace NontrivialType

def complement_closed (pred : PredicateB) :=
  ∀ x, pred.P x ↔ pred.P (NEG_vec x)

lemma complement_closed_iff_comp_closed {S} :
  complement_closed (P_of_S S) ↔ is_comp_closed S := by
  simp [complement_closed, P_of_S, PredicateB_of_SymmetricB]
  unfold is_comp_closed
  constructor
  case mp =>
    intro h w
    convert h (std_vec w) <;> simp
  case mpr =>
    intro h x
    apply h

lemma trivial_of_no_denotation {S} (hS : ¬ ∃ nt, denotation nt = S) :
  ¬ is_nontrivial_S S := by
  contrapose! hS
  exact nontrivial_denotation S hS

lemma trivial_complement_closed_polymorphisms {P S}
  (hP : P = P_of_S S) (hS : ¬ ∃ nt, denotation nt = S)
  (hclosed : complement_closed P)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  (∃ j, ∀ i x, fs i x = x j) ∨ (∃ j, ∀ i x, fs i x = NEG (x j)) ∨
    ∃ c : CertificateB P, ∀ (i : c.dom) x, fs i.1 x = c.ρ i := by
  subst hP
  apply symmetric_polymorphisms_comp_closed
  case hS => exact trivial_of_no_denotation hS
  case hcomp => exact complement_closed_iff_comp_closed.mp hclosed

lemma trivial_not_complement_closed_polymorphisms {P S}
  (hP : P = P_of_S S) (hS : ¬ ∃ nt, denotation nt = S)
  (hnotclosed : ¬ complement_closed P)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  (∃ j, ∀ i x, fs i x = x j) ∨
    ∃ c : CertificateB P, ∀ (i : c.dom) x, fs i.1 x = c.ρ i := by
  subst hP
  apply symmetric_polymorphisms_not_comp_closed
  case hS => exact trivial_of_no_denotation hS
  case hcomp =>
    contrapose! hnotclosed
    exact complement_closed_iff_comp_closed.mpr hnotclosed

end NontrivialType
