import Polymorphisms.SymmetricClassifyAtmost_mDefs
import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

lemma atmost_m_polymorphisms_only_if_nonconst {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  (hb : ∀ i : I, ∃ x, fs i x = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b := by
  sorry

end NontrivialType
