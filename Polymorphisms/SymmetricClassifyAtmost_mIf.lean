import Polymorphisms.SymmetricClassifyAtmost_mDefs
import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

lemma atmost_m_polymorphisms_if_AND' {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (J : Finset (range n)) :
  ∃ poly : PolymorphismB P n, ∀ i, poly.fs i = AND' J b := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  subst Pm
  use {
    fs i := AND' J b,
    app xs sat := by
      apply (PP _).mpr
      intro I sI
      replace sat j := (PP _).mp (sat j) I sI
      by_contra! hout
      obtain ⟨i, hout⟩ := card_eq_one.mp hout
      have hi : AND' J b (xs i) ≠ b := by
        have : i ∈ ({i | AND' J b (xs i) ≠ b} : Finset I) := by
          rw [hout]
          simp
        have := mem_filter.mp this
        exact this.right
      simp [AND'] at hi
      obtain ⟨j', hj', hjJ, hj, _⟩ := hi
      let j : range n := ⟨j', mem_range.mpr hj'⟩
      replace hjJ : j ∈ J := by simpa [j]
      replace hj : xs i j ≠ b := by simpa [j]
      apply sat j
      apply card_eq_one.mpr
      use i
      ext k
      constructor
      · intro hk
        simp
        simp at hk
        contrapose! hk
        have hk' : AND' J b (xs k) = b := by
          contrapose! hk
          have : k ∈ ({i | AND' J b (xs i) ≠ b} : Finset I) := by
            simpa
          rw [hout] at this
          simp at this
          exact this
        contrapose! hk'
        unfold AND'
        simp
        use j.val, mem_range.mp j.property
      · intro hk
        simp
        simp at hk
        subst hk
        exact hj
  }
  intro i
  simp

lemma atmost_m_polymorphisms_if_cert {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} {fs : range P.m → (range n → range 2) → range 2}
  {I : Finset (range P.m)} (sI : #I = m - w) (hI : ∀ i ∈ I, fs i = CONST (NEG b)) :
  ∃ poly : PolymorphismB P n, poly.fs = fs := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  subst Pm
  use {
    fs := fs,
    app xs sat := by
      apply (PP _).mpr
      intro K sK
      have hint : #(K ∩ I) ≥ 2 := by
        have := card_union_add_card_inter K I
        have : #(K ∪ I) ≤ P.m := calc
          #(K ∪ I) ≤ #((range P.m).attach) := by
            apply card_le_card
            intro i hi
            apply mem_attach
          _ = P.m := by
            rw [card_attach, card_range]
        omega
      suffices #{i : K | fs i (xs i) ≠ b} ≥ #(K ∩ I) by
        omega
      simp
      let L : Finset K := {i : K | i.val ∈ I}
      have : #(K ∩ I) = #L := by
        let e : {x // x ∈ K ∩ I} ≃ {x // x ∈ L} := {
          toFun i := by
            have := mem_inter.mp i.property
            use ⟨i, ?_⟩
            simp [L]
            · exact this.right
            · exact this.left
          invFun i := by
            use ⟨i, ?_⟩
            apply mem_inter.mpr
            constructor
            · simp
            · simp
              have := i.property
              unfold L at this
              have := mem_filter.mp this
              exact this.right
            · simp
          left_inv := by
            intro i
            simp
          right_inv := by
            intro i
            simp
        }
        apply card_eq_of_equiv e
      rw [this]
      apply card_le_card
      intro i hi
      simp [L] at hi
      simp [congrFun (hI i hi) (xs i), CONST]
      exact (ReductionTo1.neg₂_dichotomy rfl).mpr rfl
  }

end NontrivialType
