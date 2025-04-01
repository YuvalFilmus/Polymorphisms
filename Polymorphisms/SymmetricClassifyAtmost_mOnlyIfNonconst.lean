import Polymorphisms.SymmetricClassifyAtmost_mDefs
import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

-- next: reduce to a statement about sets

lemma atmost_m_polymorphisms_only_if_nonconst' {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  {xfsb : I → range n → range 2} (hxfsb : ∀ i : I, fs i (xfsb i) = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b := by
  sorry

lemma atmost_m_polymorphisms_only_if_nonconst {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  (hb : ∀ i : I, ∃ x, fs i x = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b := by
  let xfsb (i : I) := (hb i).choose
  let hxfsb (i : I) : fs i (xfsb i) = b := (hb i).choose_spec
  exact atmost_m_polymorphisms_only_if_nonconst' hw hI hfs hxfsb

end NontrivialType
