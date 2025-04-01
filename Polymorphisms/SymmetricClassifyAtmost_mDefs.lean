import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

def AND' {n} (J : Finset (range n)) (b : range 2) (x : range n → range 2) : range 2 :=
  if ∀ j ∈ J, x j = b then b else NEG b

lemma AND'_def {n} {J : Finset (range n)} {b : range 2} {x : range n → range 2} :
  AND' J b x = b ↔ ∀ j ∈ J, x j = b := by
  constructor
  · intro h
    intro j hj
    contrapose! h
    simp [AND']
    use j.val, mem_range.mp j.property
    constructor
    exact hj
    constructor
    exact h
    exact (NEG_ne b).symm
  · intro h
    unfold AND'
    split
    rfl
    rfl

def CONST {n} (b : range 2) (_ : range n → range 2) : range 2 := b

lemma AND'_ne_CONST {n} (b : range 2) (J : Finset (range n)) : AND' J b ≠ CONST (NEG b) := by
  by_contra! h
  have := congrFun h (fun _ ↦ b)
  simp [AND', CONST] at this
  apply NEG_ne
  assumption

lemma AND'_eq_AND' {n} (b : range 2) (J J' : Finset (range n)) (h : AND' J b = AND' J' b) :
  J = J' := by
  apply Subset.antisymm
  · let x (j : range n) := if j ∈ J' then b else NEG b
    replace h := congrFun h x
    have : AND' J' b x = b := by
      apply AND'_def.mpr
      intro j hj
      simp [x, hj]
    rw [this] at h
    have := AND'_def.mp h
    intro j hj
    have := this j hj
    simp [x, (NEG_ne b).symm] at this
    exact this
  · let x (j : range n) := if j ∈ J then b else NEG b
    replace h := congrFun h x
    have : AND' J b x = b := by
      apply AND'_def.mpr
      intro j hj
      simp [x, hj]
    rw [this] at h
    have := AND'_def.mp h.symm
    intro j hj
    have := this j hj
    simp [x, (NEG_ne b).symm] at this
    exact this

end NontrivialType
