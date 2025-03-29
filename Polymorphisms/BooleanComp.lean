import Polymorphisms.Boolean
import Polymorphisms.SymmetricDefs
open Finset

namespace PredicateB

def complement (pred : PredicateB) : PredicateB := {
  m := pred.m,
  hm := pred.hm,
  P x := pred.P (NEG_vec x),
  full i σ := by
    obtain ⟨x, Px, hx⟩ := pred.full i (NEG σ)
    use NEG_vec x
    simp
    constructor
    · assumption
    · simp [NEG_vec, hx]
  dep i := by
    obtain ⟨x, y, Px, Py, h⟩ := pred.dep i
    use NEG_vec x, NEG_vec y
    constructor
    · simpa
    constructor
    · simpa
    · intro i' hii'
      simp [NEG_vec]
      congr
      exact h i' hii'
}

@[simp]
lemma complement_complement {pred : PredicateB} :
  pred.complement.complement = pred := by
  simp [complement]

end PredicateB

namespace SymmetricB

def complement (S : SymmetricB) : SymmetricB := {
  m := S.m,
  W := { S.m-w | w ∈ S.W },
  notall0 := by
    obtain ⟨w, w_in, hw⟩ := S.notall1
    use ⟨S.m - w, ?_⟩
    constructor
    · simp
      use w
      simp
      constructor
      omega
      assumption
    · simpa
    apply mem_range.mpr
    omega
  notall1 := by
    obtain ⟨w, w_in, hw⟩ := S.notall0
    use ⟨S.m - w, ?_⟩
    constructor
    · simp
      use w
      simp
      constructor
      exact mem_range.mp w.property
      assumption
    · simp
      constructor
      have := symmetric_m_ge_2 S
      omega
      assumption
    apply mem_range.mpr
    omega
  notfull := by
    obtain ⟨w, hw⟩ := S.notfull
    use ⟨S.m - w, ?_⟩
    simp
    intro w' hw' Pw'
    by_contra! h
    apply hw
    convert Pw'
    have := mem_range.mp w.property
    omega
    apply mem_range.mpr
    omega
}

@[simp]
lemma complement_complement {S : SymmetricB} :
  S.complement.complement = S := by
  simp [complement]
  ext
  case m =>
    simp
  case W =>
    simp
    ext i
    simp
    constructor
    case mp =>
      rintro ⟨i', ⟨hi', Wi'⟩, _, hii'⟩
      convert Wi'
      omega
    case mpr =>
      intro Wi
      use i.val
      constructor
      · use mem_range.mp i.property
      constructor
      omega
      have := mem_range.mp i.property
      omega

end SymmetricB

lemma complement_symmetric (S : SymmetricB) :
  P_of_S S.complement = (P_of_S S).complement := by
  simp [SymmetricB.complement, PredicateB.complement, P_of_S, PredicateB_of_SymmetricB]
  funext x
  apply propext
  constructor
  · rintro ⟨w, ⟨hw, Pw⟩, hw'⟩
    convert Pw
    simp [comp]
    omega
  · intro Pw
    use S.m - wt x
    constructor
    use (by omega)
    convert Pw
    have := mem_range.mp (wt x).property
    omega

@[simp]
lemma S_atmost_comp {m b : ℕ} {hlb : 0 < b} {hub : b < m} :
  (S_atmost hlb hub).complement = @S_atleast m (m-b) (by omega) (by omega) := by
  simp [SymmetricB.complement, S_atmost, S_atleast]
  congr
  funext w
  apply propext
  constructor
  case mp =>
    intros
    omega
  case mpr =>
    intro hw
    use m-w
    constructor
    omega
    constructor
    omega
    have := mem_range.mp w.property
    omega

@[simp]
lemma S_atleast_comp {m b : ℕ} {hlb : 0 < b} {hub : b < m} :
  (S_atleast hlb hub).complement = @S_atmost m (m-b) (by omega) (by omega) := by
  symm
  rw [←@SymmetricB.complement_complement (S_atmost _ _)]
  congr
  simp
  congr
  omega

@[simp]
lemma S_atmost_m_comp {m b : ℕ} {hub : b+1 < m} :
  (S_atmost_m hub).complement = @S_atleast_0 m (m-b) (by omega) (by omega) := by
  simp [SymmetricB.complement, S_atmost_m, S_atleast_0]
  congr
  funext w
  apply propext
  constructor
  case mp =>
    rintro ⟨w', hw', hww'⟩
    simp at hw'
    omega
  case mpr =>
    intro hw
    have := mem_range.mp w.property
    use ⟨m - w, ?_⟩
    constructor
    simp
    omega
    simp
    omega
    apply mem_range.mpr
    omega

@[simp]
lemma S_atleast_0_comp {m b : ℕ} {hlb : 1 < b} {hub : b ≤ m} :
  (S_atleast_0 hlb hub).complement = @S_atmost_m m (m-b) (by omega) := by
  symm
  rw [←@SymmetricB.complement_complement (S_atmost_m _)]
  congr
  simp
  congr
  omega
