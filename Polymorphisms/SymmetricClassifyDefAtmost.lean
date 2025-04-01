import Polymorphisms.SymmetricClassify
import Polymorphisms.BooleanComp
open Finset

namespace NontrivialType

lemma wt_set {m} (x : range m → range 2) :
  wt x = #({i | x i = b1} : Finset _) := by
  let S0 : Finset _ := {i | x i = b0}
  let S1 : Finset _ := {i | x i = b1}
  have Sdisjoint : Disjoint S0 S1 := by
    apply disjoint_left.mpr
    intro a ha0 ha1
    simp [S0, b0] at ha0
    simp [S1, b1] at ha1
    have := Eq.trans ha0.symm ha1
    contradiction
  have Sunion : S0 ∪ S1 = univ := by
    apply eq_univ_of_forall
    intro i
    cases of_range_2B (x i)
    case a.inl h =>
      apply mem_union_left
      simpa [S0]
    case a.inr h =>
      apply mem_union_right
      simpa [S1]
  simp [wt]
  calc
    ∑ i ∈ range m, coe_vec x i = ∑ i ∈ (univ : Finset (range m)), coe_vec x i := by
      exact Eq.symm (sum_coe_sort (range m) (coe_vec x))
    _ = ∑ i ∈ S0, coe_vec x i + ∑ i ∈ S1, coe_vec x i := by
      rw [←Sunion, sum_union]
      assumption
    _ = 0 + ∑ i ∈ S1, coe_vec x i := by
      congr
      apply sum_eq_zero_iff.mpr
      intro i hi
      simp [S0, b0] at hi
      simp [coe_vec, hi]
    _ = #S1 • 1 := by
      rw [zero_add, ←sum_const]
      apply sum_congr rfl
      intro i hi
      simp [S1, b1] at hi
      simp [coe_vec, hi]
      apply mem_range.mp i.property
    _ = #({i | x i = b1} : Finset _) := by
      aesop

def extract_subset {m w} {S : Finset (range m)} (hS : #S > w) :
  ∃ I, I ⊆ S ∧ #I = w + 1 := by
  induction S using Finset.induction
  case empty =>
    simp at hS
  case insert i T hi hind =>
  by_cases #T > w
  case pos h =>
    obtain ⟨I, sI, cI⟩ := hind h
    use I
    constructor
    intro j hj
    apply mem_insert_of_mem
    exact sI hj
    exact cI
  case neg h =>
    use insert i T
    simp [card_insert_of_not_mem hi]
    simp [card_insert_of_not_mem hi] at hS
    omega

lemma atmost_def_1 {P m w hm hw} (h : P = P_of_S (atmost m w b1 hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+1 → #{i : I | x i ≠ b1} ≠ 0 := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_atmost, b1]
  intro x
  constructor
  case mp =>
    intro hm I hI
    by_contra! h
    have : I ⊆ ({i | x i = b1} : Finset _) := by
      intro i hi
      simp [b1]
      have := @filter_eq_empty_iff.mp h ⟨i, hi⟩
      simp at this
      assumption
    have := card_le_card this
    rw [hI, ←wt_set] at this
    omega
  case mpr =>
    intro h
    by_contra! hw
    rw [wt_set] at hw
    obtain ⟨I, sI, cI⟩ := extract_subset hw
    apply h I cI
    apply filter_eq_empty_iff.mpr
    intro i hi
    simp
    have := sI i.property
    simp at this
    rw [this]
    simp [b1]

lemma wt_complement (S : SymmetricB) (x) :
  wt x ∈ S.W ↔ wt (NEG_vec x) ∈ S.complement.W := by
  have := mem_range.mp (wt x).property
  constructor
  case mp =>
    intro h
    simp [wt_NEG_vec, comp, comp_val, SymmetricB.complement]
    use wt x
    constructor
    use (by omega)
    rfl
  case mpr =>
    intro h
    simp only [NEG_vec, SymmetricB.complement, mem_filter] at h
    obtain ⟨w, Pw, hw⟩ := h.right
    convert Pw
    simp [comp] at hw
    have := mem_range.mp w.property
    apply Subtype.coe_eq_of_eq_mk
    omega

lemma atmost_def {P m w b hm hw} (h : P = P_of_S (atmost m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+1 → #{i : I | x i ≠ b} ≠ 0 := by
  cases of_range_2B b
  case inr hb =>
    subst hb
    apply atmost_def_1 <;> assumption
  case inl hb =>
  subst hb
  subst h
  simp [P_of_S, PredicateB_of_SymmetricB, denotation, b0]
  constructor
  simp [S_atleast]
  intro x
  rw [wt_complement]
  have : wt (NEG_vec x) ∈ (@S_atleast m (m-w) (by omega) (by omega)).complement.W ↔ wt (NEG_vec x) ∈ (@S_atmost m w (by omega) (by omega)).W := by
      constructor
      all_goals (intro h; convert h; simp; congr; omega; simp; congr; omega)
  rw [this]
  have := (@atmost_def_1 (P_of_S (@S_atmost m w (by omega) (by omega))) m w (by omega) (by omega) rfl).right (NEG_vec x)
  simp only [P_of_S, PredicateB_of_SymmetricB] at this
  rw [this]
  simp [NEG_vec, NEG, b0, b1]
  rfl

lemma atmost_m_def_1 {P m w hm hw} (h : P = P_of_S (atmost_m m w b1 hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+2 → #{i : I | x i ≠ b1} ≠ 1 := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_atmost_m, b1]
  intro x
  constructor
  case mp =>
    intro hm I hI
    by_contra! hI'
    obtain ⟨i, hiI'⟩ := card_eq_one.mp hI'
    have hi : x i = b0 := by
      cases of_range_2B (x i)
      case inl h => exact h
      case inr h =>
        exfalso
        have : i ∈ ({i} : Finset _) := mem_singleton.mpr rfl
        simp [←hiI', h, b1] at this
    have hI'' i' (hi' : i' ∈ I) (hii' : i' ≠ i) : x i' = b1 := by
      have : ⟨i', hi'⟩ ∉ ({i} : Finset _) := by
        apply not_mem_singleton.mpr
        contrapose! hii'
        rw [←hii']
      simp [←hiI'] at this
      simp [this, b1]
    cases hm
    case inl hm =>
      suffices w + 1 ≤ wt x by omega
      have : I.erase i ⊆ ({i | x i = b1} : Finset _) := by
        intro i' hi'
        simp
        simp at hi'
        exact hI'' i' hi'.right hi'.left
      have := card_le_card this
      simp [card_erase_of_mem i.property, hI] at this
      convert this
      apply wt_set
    case inr hm =>
      have := wt_m.mp (Subtype.coe_eq_of_eq_mk hm) i
      simp [b0] at hi
      simp [b1, hi] at this
  case mpr =>
    intro h
    by_contra! hw
    have : ∃ i, x i = b0 := by
      by_contra! h
      replace hw := hw.right
      contrapose! hw
      apply Subtype.coe_eq_iff.mpr
      use (by apply mem_range.mpr; omega)
      apply wt_m.mpr
      intro i
      cases of_range_2B (x i)
      case inl hxi => have := h i; contradiction
      case inr hxi => assumption
    obtain ⟨i, hi⟩ := this
    have : w+1 ≤ wt x := by omega
    rw [wt_set] at this
    obtain ⟨I', sI', cI'⟩ := extract_subset this
    have hiI' : i ∉ I' := by
      by_contra! h
      have := sI' h
      simp [hi, b0, b1] at this
    let I := insert i I'
    have cI : #I = w + 2 := by
      simp [I, card_insert_of_not_mem hiI']
      assumption
    apply h I cI
    apply card_eq_one.mpr
    use ⟨i, by aesop⟩
    apply eq_singleton_iff_unique_mem.mpr
    constructor
    · simp [hi, b0]
    · intro i'
      simp
      intro hi'
      contrapose! hi'
      have : i'.val ∈ I' := by
        aesop
      have := sI' this
      simp [b1] at this
      assumption

lemma atmost_m_def {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ ∀ (I : Finset (range P.m)), #I = w+2 → #{i : I | x i ≠ b} ≠ 1 := by
  cases of_range_2B b
  case inr hb =>
    subst hb
    apply atmost_m_def_1 <;> assumption
  case inl hb =>
  subst hb
  subst h
  simp [P_of_S, PredicateB_of_SymmetricB, denotation, b0]
  constructor
  simp [S_atleast_0]
  intro x
  rw [wt_complement]
  have : wt (NEG_vec x) ∈ (@S_atleast_0 m (m-w) (by omega) (by omega)).complement.W ↔ wt (NEG_vec x) ∈ (@S_atmost_m m w (by omega)).W := by
      constructor
      all_goals (intro h; convert h; simp; congr; omega; simp; congr; omega)
  rw [this]
  have := (@atmost_m_def_1 (P_of_S (@S_atmost_m m w (by omega))) m w (by omega) (by omega) rfl).right (NEG_vec x)
  simp only [P_of_S, PredicateB_of_SymmetricB] at this
  rw [this]
  simp [NEG_vec, NEG, b0, b1]
  rfl

lemma atmost_def_1' {P m w hm hw} (h : P = P_of_S (atmost m w b1 hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ #{i | x i = b1} ≤ w := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_atmost, b1]
  intro x
  rw [wt_set]
  simp [b1]

lemma atmost_def' {P m w b hm hw} (h : P = P_of_S (atmost m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ #{i | x i = b} ≤ w := by
  cases of_range_2B b
  case inr hb =>
    subst hb
    apply atmost_def_1' <;> assumption
  case inl hb =>
  subst hb
  subst h
  simp [P_of_S, PredicateB_of_SymmetricB, denotation, b0]
  constructor
  simp [S_atleast]
  intro x
  rw [wt_complement]
  have : wt (NEG_vec x) ∈ (@S_atleast m (m-w) (by omega) (by omega)).complement.W ↔ wt (NEG_vec x) ∈ (@S_atmost m w (by omega) (by omega)).W := by
      constructor
      all_goals (intro h; convert h; simp; congr; omega; simp; congr; omega)
  rw [this]
  have := (@atmost_def_1' (P_of_S (@S_atmost m w (by omega) (by omega))) m w (by omega) (by omega) rfl).right (NEG_vec x)
  simp only [P_of_S, PredicateB_of_SymmetricB] at this
  rw [this]
  simp [NEG_vec, NEG, b0, b1]
  rfl

lemma atmost_m_def_1' {P m w hm hw} (h : P = P_of_S (atmost_m m w b1 hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ #{i | x i = b1} ≤ w ∨ #{i | x i = b1} = m := by
  subst h
  simp [denotation, P_of_S, PredicateB_of_SymmetricB, S_atmost_m, b1]
  intro x
  rw [wt_set]
  simp [b1]

lemma atmost_m_def' {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation) :
  P.m = m ∧
  ∀ x, P.P x ↔ #{i | x i = b} ≤ w ∨ #{i | x i = b} = m := by
  cases of_range_2B b
  case inr hb =>
    subst hb
    apply atmost_m_def_1' <;> assumption
  case inl hb =>
  subst hb
  subst h
  simp [P_of_S, PredicateB_of_SymmetricB, denotation, b0]
  constructor
  simp [S_atleast_0]
  intro x
  rw [wt_complement]
  have : wt (NEG_vec x) ∈ (@S_atleast_0 m (m-w) (by omega) (by omega)).complement.W ↔ wt (NEG_vec x) ∈ (@S_atmost_m m w (by omega)).W := by
      constructor
      all_goals (intro h; convert h; simp; congr; omega; simp; congr; omega)
  rw [this]
  have := (@atmost_m_def_1' (P_of_S (@S_atmost_m m w (by omega))) m w (by omega) (by omega) rfl).right (NEG_vec x)
  simp only [P_of_S, PredicateB_of_SymmetricB] at this
  rw [this]
  simp [NEG_vec, NEG, b0, b1]
  rfl

end NontrivialType
