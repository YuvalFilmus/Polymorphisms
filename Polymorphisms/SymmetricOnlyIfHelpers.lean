import Polymorphisms.Basic
import Polymorphisms.SymmetricDefs
import Polymorphisms.BooleanReductions
open Finset

lemma construct_atmost {S : SymmetricB} {w₀ : range (S.m+1)}
  (hw₀ : ∀ w, w ∈ S.W ↔ w ≤ w₀) :
  is_nontrivial_S S := by
  have hlb : 0 < w₀.1 := by
    by_contra! h
    obtain ⟨w, w_in, hw⟩ := S.notall0
    replace w_in := (hw₀ w).mp w_in
    replace w_in : w.1 ≤ w₀.1 := w_in
    omega
  have hub : w₀.1 < S.m := by
    by_contra! h
    obtain ⟨w, hw⟩ := S.notfull
    apply hw
    apply (hw₀ w).mpr
    apply Subtype.coe_le_coe.mp
    have := mem_range.mp w₀.property
    have := mem_range.mp w.property
    omega
  right; right; left
  use S.m, w₀, hlb, hub
  ext; rfl
  simp [S_atmost]
  apply Finset.ext_iff.mpr
  intro w
  simp
  apply hw₀

lemma construct_atleast {S : SymmetricB} {w₀ : range (S.m+1)}
  (hw₀ : ∀ w, w ∈ S.W ↔ w₀ ≤ w) :
  is_nontrivial_S S := by
  have hlb : 0 < w₀.1 := by
    by_contra! h
    obtain ⟨w, hw⟩ := S.notfull
    apply hw
    apply (hw₀ w).mpr
    apply Subtype.coe_le_coe.mp
    omega
  have hub : w₀.1 < S.m := by
    by_contra! h
    obtain ⟨w, w_in, hw⟩ := S.notall1
    replace w_in := (hw₀ w).mp w_in
    replace w_in : w₀.1 ≤ w.1 := w_in
    omega
  right; right; right; left
  use S.m, w₀, hlb, hub
  ext; rfl
  simp [S_atleast]
  apply Finset.ext_iff.mpr
  intro w
  simp
  apply hw₀

lemma construct_atmost_m {S : SymmetricB} {w₀ : range (S.m+1)}
  (hw₀ : ∀ w, w ∈ S.W ↔ (w ≤ w₀ ∨ w = range_l)) :
  is_nontrivial_S S := by
  have hub : w₀+1 < S.m := by
    by_contra! h
    obtain ⟨w, hw⟩ := S.notfull
    apply hw
    apply (hw₀ w).mpr
    by_cases w = range_l
    case pos => right; assumption
    case neg hw =>
    left
    have : w.1 ≠ S.m := by contrapose! hw; exact Subtype.coe_eq_of_eq_mk hw
    apply Subtype.coe_le_coe.mp
    have := mem_range.mp w.property
    omega
  right; right; right; right; left
  use S.m, w₀, hub
  ext; rfl
  simp [S_atmost_m]
  apply Finset.ext_iff.mpr
  intro w
  simp
  simp [range_l] at hw₀
  apply hw₀
  apply mem_range.mp w.property

lemma construct_atleast_0 {S : SymmetricB} {w₀ : range (S.m+1)}
  (hw₀ : ∀ w, w ∈ S.W ↔ (w₀ ≤ w ∨ w = range_0)) :
  is_nontrivial_S S := by
  have hlb : 1 < w₀.1 := by
    by_contra! h
    obtain ⟨w, hw⟩ := S.notfull
    apply hw
    apply (hw₀ w).mpr
    by_cases w = range_0
    case pos => right; assumption
    case neg hw =>
    left
    simp [range_0] at hw
    have : w.1 ≠ 0 := by contrapose! hw; exact Subtype.coe_eq_of_eq_mk hw
    apply Subtype.coe_le_coe.mp
    omega
  have hub : w₀.1 ≤ S.m := by
    have := mem_range.mp w₀.property
    omega
  right; right; right; right; right
  use S.m, w₀, hlb, hub
  ext; rfl
  simp [S_atleast_0]
  apply Finset.ext_iff.mpr
  intro w
  simp
  simp [range_0] at hw₀
  apply hw₀
  apply mem_range.mp w.property

lemma wt_0_to_1 {m} {x : range m → range 2} {i} (h : x i = b0) :
  wt (set_coord_to i b1 x) = (wt x).1 + 1 := calc
  wt (set_coord_to i b1 x) = ∑ j ∈ range m, (coe_vec (set_coord_to i b1 x)) j := by simp [wt]
  _ = (coe_vec (set_coord_to i b1 x)) i + ∑ j ∈ (range m).erase i, (coe_vec (set_coord_to i b1 x)) j := by
    rw [add_sum_erase]
    exact i.property
  _ = 1 + ∑ j ∈ (range m).erase i, (coe_vec (set_coord_to i b1 x)) j := by
    congr
    simp [coe_vec, set_coord_to, mem_range.mp i.property, b1]
  _ = 1 + ∑ j ∈ (range m).erase i, coe_vec x j := by
    congr 1
    apply sum_congr rfl
    intro j hj
    simp at hj
    simp [coe_vec, set_coord_to, hj]
    split
    case _ h => exfalso; apply hj.1; rw [←h]
    case _ h => rfl
  _ = 1 + 0 + ∑ j ∈ (range m).erase i, coe_vec x j := by omega
  _ = 1 + coe_vec x i + ∑ j ∈ (range m).erase i, coe_vec x j := by
    congr 2
    simp [coe_vec, mem_range.mp i.property, h, b0]
  _ = 1 + (coe_vec x i + ∑ j ∈ (range m).erase i, coe_vec x j) := by
    rw [add_assoc]
  _ = 1 + ∑ j ∈ range m, coe_vec x j := by
    congr
    rw [add_sum_erase]
    exact i.property
  _ = 1 + (wt x).1 := by simp [wt]
  _ = (wt x).1 + 1 := by rw [add_comm]

lemma wt_1_to_0 {m} {x : range m → range 2} {i} (h : x i = b1) :
  wt x = (wt (set_coord_to i b0 x)).1 + 1 := calc
  wt x = ∑ j ∈ range m, coe_vec x j := by simp [wt]
  _ = coe_vec x i + ∑ j ∈ (range m).erase i, coe_vec x j := by
    rw [add_sum_erase]
    exact i.property
  _ = 1 + ∑ j ∈ (range m).erase i, coe_vec x j := by
    congr
    simp [coe_vec, mem_range.mp i.property, h, b1]
  _ = 1 + (0 + ∑ j ∈ (range m).erase i, coe_vec x j) := by omega
  _ = 1 + (0 + ∑ j ∈ (range m).erase i, coe_vec (set_coord_to i b0 x) j) := by
    congr 2
    apply sum_congr rfl
    intro j hj
    simp at hj
    simp [coe_vec, set_coord_to, hj]
    split
    case _ h => exfalso; apply hj.1; rw [←h]
    case _ h => rfl
  _ = 1 + (coe_vec (set_coord_to i b0 x) i + ∑ j ∈ (range m).erase i, coe_vec (set_coord_to i b0 x) j) := by
    congr 2
    simp [coe_vec, set_coord_to, mem_range.mp i.property, b0]
  _ = 1 + ∑ j ∈ range m, coe_vec (set_coord_to i b0 x) j := by
    congr
    rw [add_sum_erase]
    exact i.property
  _ = 1 + (wt (set_coord_to i b0 x)).1 := by
    simp [wt]
  _ = (wt (set_coord_to i b0 x)).1 + 1 := by omega

lemma nontrivial_weight_or_nontrivial (S) :
  (∃ w ∈ S.W, w.1 > 0 ∧ w.1 < S.m) ∨ is_nontrivial_S S := by
  by_cases ∃ w ∈ S.W, w.1 > 0 ∧ w.1 < S.m
  case pos h => left; exact h
  case neg h =>
  replace h : ∀ w ∈ S.W, w.1 = 0 ∨ w.1 = S.m := by
    intro w hw
    contrapose! h
    use w
    constructor
    exact hw
    have := mem_range.mp w.property
    constructor <;> omega
  right; right; right; right; right; left
  use S.m, 0, by
    have := symmetric_m_ge_2 S
    omega
  ext
  case m => rfl
  case W =>
    simp
    apply Finset.ext_iff.mpr
    intro w
    constructor
    · intro hw
      simp [S_atmost_m]
      exact h w hw
    · intro hw
      simp [S_atmost_m] at hw
      cases hw
      case inl hw =>
        by_contra! w_notin
        obtain ⟨w', w'_in, hw'⟩ := S.notall1
        cases h w' w'_in
        case inl hw' =>
          apply w_notin
          convert w'_in
          apply Subtype.coe_eq_of_eq_mk
          rw [hw, hw']
        case inr hw' => omega
      case inr hw =>
        have hm := symmetric_m_ge_2 S
        by_contra! w_notin
        obtain ⟨w', w'_in, hw'⟩ := S.notall0
        cases h w' w'_in
        case inl hw' =>
          apply w_notin
          convert w'_in
          apply Subtype.coe_eq_of_eq_mk
          rw [hw, hw']
          omega
        case inr hw' =>
          apply w_notin
          convert w'_in
          apply Subtype.coe_eq_of_eq_mk
          rw [hw, hw']

instance (S : SymmetricB) : AtLeast3 (S.m+1) :=
  ⟨by have := symmetric_m_ge_2 S; omega⟩

lemma m_ge_3_or_nontrivial (S) :
  S.m ≥ 3 ∨ is_nontrivial_S S := by
  by_cases S.m = 2
  case pos hm =>
    right
    cases nontrivial_weight_or_nontrivial S
    case inr h => exact h
    case inl h =>
    obtain ⟨w, hw, hw₀, hw₁⟩ := h
    have wval : w.1 = 1 := by omega
    let r0 : range (S.m+1) := ⟨0, by apply mem_range.mpr; omega⟩
    let r1 : range (S.m+1) := ⟨1, by apply mem_range.mpr; omega⟩
    let r2 : range (S.m+1) := ⟨2, by apply mem_range.mpr; omega⟩
    have w_cases (w : range (S.m+1)) : w = r0 ∨ w = r1 ∨ w = r2 := by
      let w_val := w.1
      have hw_val : w.1 = w_val := by simp [w_val]
      match w_val with
      | 0 => left; apply Subtype.coe_eq_of_eq_mk; assumption
      | 1 => right; left; apply Subtype.coe_eq_of_eq_mk; assumption
      | 2 => right; right; apply Subtype.coe_eq_of_eq_mk; assumption
      | n+3 => have := mem_range.mp w.property; omega
    replace hr1 : r1 ∈ S.W := by
      simp [r1]; convert hw; symm; assumption
    by_cases r0 ∈ S.W
    case pos hr0 =>
      by_cases r2 ∈ S.W
      case pos hr2 =>
        obtain ⟨w, hw⟩ := S.notfull
        exfalso
        apply hw
        cases w_cases w
        case inl h => subst h; assumption
        case inr h =>
        cases h
        case inl h => subst h; assumption
        case inr h => subst h; assumption
      case neg hr2 =>
        right; right; left
        use S.m, 1, by omega, by omega
        ext; rfl; simp [S_atmost]; apply Finset.ext_iff.mpr
        intro w; simp
        cases w_cases w
        case inl h => subst h; simp [r0]; assumption
        case inr h =>
        cases h
        case inl h => subst h; simp [r1]; assumption
        case inr h => subst h; simp [r2]; assumption
    case neg hr0 =>
      by_cases r2 ∈ S.W
      case pos hr2 =>
        right; right; right; left
        use S.m, 1, by omega, by omega
        ext; rfl; simp [S_atleast]; apply Finset.ext_iff.mpr
        intro w; simp
        cases w_cases w
        case inl h => subst h; simp [r0]; assumption
        case inr h =>
        cases h
        case inl h => subst h; simp [r1]; assumption
        case inr h => subst h; simp [r2]; assumption
      case neg hr2 =>
        right; left
        use S.m, symmetric_m_ge_2 S
        ext; rfl; simp [S_odd]; apply Finset.ext_iff.mpr
        intro w; simp
        suffices w ∈ S.W ↔ w.1 % 2 = 1 by
          have odd_def := @Nat.odd_iff w.1
          tauto
        cases w_cases w
        case inl h => subst h; simp [r0]; assumption
        case inr h =>
        cases h
        case inl h => subst h; simp [r1]; assumption
        case inr h => subst h; simp [r2]; assumption
  case neg =>
    have := symmetric_m_ge_2 S
    omega

lemma w_inc_lemma {m : ℕ} {W : Finset (range (m+1))} (hW : W.Nonempty)
  (w_inc : ∀ {w : range (m+1)} (hw : w.1 < m), w ∈ W → ⟨w+1, by apply mem_range.mpr; omega⟩ ∈ W) :
  ∃ (w₀ : range (m+1)), ∀ (w : range (m+1)), w ∈ W ↔ w₀ ≤ w := by
  let w₀ := min' W hW
  have w₀_prop : w₀ ∈ W := by apply min'_mem
  have hnotin (w : range (m+1)) (hw : w < w₀) : w ∉ W := by
    contrapose! hw
    apply min'_le
    assumption
  have hin (w : range (m+1)) (hw : w₀ ≤ w) : w ∈ W := by
    revert w hw
    by_contra! h
    let W' : Finset _ := { w | w₀ ≤ w ∧ w ∉ W }
    have : W'.Nonempty := by
      obtain ⟨w, hw⟩ := h
      use w
      simpa [W']
    let w₁ := min' W' this
    have w₁_prop : w₁ ∈ W' := by apply min'_mem
    have hw₀w₁ : w₀ ≠ w₁ := by
      contrapose! w₁_prop
      simp [W']
      simp [w₁_prop]
      rwa [←w₁_prop]
    simp [W'] at w₁_prop
    let w₁pred : range (m+1) := ⟨w₁-1, by apply mem_range.mpr; have := mem_range.mp w₁.property; omega⟩
    have : w₀.1 ≠ w₁.1 := by contrapose! hw₀w₁; apply Subtype.eq_iff.mpr; assumption
    have : w₀.1 ≤ w₁.1 := Subtype.coe_le_coe.mpr w₁_prop.1
    have hw₀w₁pred : w₀ ≤ w₁pred := by
      simp [w₁pred]
      apply Subtype.coe_le_coe.mp
      simp
      omega
    have hw₁predw₁ : w₁pred < w₁ := by
      simp [w₁pred]
      apply Subtype.coe_lt_coe.mp
      simp
      omega
    have hsucc : w₁ = w₁pred.1 + 1 := by
      simp [w₁pred]
      omega
    have hw₁pred : w₁pred ∉ W' := by
      by_contra! h
      have : w₁ ≤ w₁pred := by simp [w₁]; apply min'_le; assumption
      have : w₁ < w₁ := lt_of_le_of_lt this hw₁predw₁
      simp at this
    simp [W'] at hw₁pred
    replace hw₁pred := hw₁pred hw₀w₁pred
    have : w₁pred < m := by have := mem_range.mp w₁.property; omega
    have := w_inc this hw₁pred
    apply w₁_prop.2
    convert this
  use w₀
  intro w
  constructor
  · intro hw
    contrapose! hw
    apply hnotin
    assumption
  · exact hin w

lemma w_dec_lemma {m : ℕ} {W : Finset (range (m+1))} (hW : W.Nonempty)
  (w_dec : ∀ {w : range (m+1)} (hw : 0 < w.1), w ∈ W → ⟨w-1, by apply mem_range.mpr; have := mem_range.mp w.property; omega⟩ ∈ W) :
  ∃ (w₀ : range (m+1)), ∀ (w : range (m+1)), w ∈ W ↔ w ≤ w₀ := by
  let w₀ := max' W hW
  have w₀_prop : w₀ ∈ W := by apply max'_mem
  have hnotin (w : range (m+1)) (hw : w₀ < w) : w ∉ W := by
    contrapose! hw
    apply le_max'
    assumption
  have hin (w : range (m+1)) (hw : w ≤ w₀) : w ∈ W := by
    revert w hw
    by_contra! h
    let W' : Finset _ := { w | w ≤ w₀ ∧ w ∉ W }
    have : W'.Nonempty := by
      obtain ⟨w, hw⟩ := h
      use w
      simpa [W']
    let w₁ := max' W' this
    have w₁_prop : w₁ ∈ W' := by apply max'_mem
    have : w₁.1 ≤ w₀.1 := by
      simp [W'] at w₁_prop
      exact w₁_prop.1
    have hw₀w₁ : w₀ ≠ w₁ := by
      contrapose! w₁_prop
      simp [W']
      simp [w₁_prop]
      rwa [←w₁_prop]
    have : w₁.1 ≠ w₀.1 := by contrapose! hw₀w₁; apply Subtype.eq; symm; assumption
    have : w₁.1 < w₀.1 := by omega
    have := mem_range.mp w₀.property;
    simp [W'] at w₁_prop
    let w₁succ : range (m+1) := ⟨w₁+1, by apply mem_range.mpr; omega⟩
    have : w₀.1 ≠ w₁.1 := by contrapose! hw₀w₁; apply Subtype.eq_iff.mpr; assumption
    have : w₀.1 ≥ w₁.1 := Subtype.coe_le_coe.mpr w₁_prop.1
    have hw₀w₁succ : w₀ ≥ w₁succ := by
      simp [w₁succ]
      apply Subtype.coe_le_coe.mp
      simp
      omega
    have hw₁succw₁ : w₁succ > w₁ := by
      simp [w₁succ]
      apply Subtype.coe_lt_coe.mp
      simp
    have hsucc : w₁ = w₁succ.1 - 1 := by
      simp [w₁succ]
    have hw₁succ : w₁succ ∉ W' := by
      by_contra! h
      have : w₁ ≥ w₁succ := by simp [w₁]; apply le_max'; assumption
      have : w₁ > w₁ := gt_of_ge_of_gt this hw₁succw₁
      simp at this
    simp [W'] at hw₁succ
    replace hw₁succ := hw₁succ hw₀w₁succ
    have : range_0 < w₁succ := by
      simp [w₁succ]
      apply Subtype.coe_lt_coe.mp
      simp [range_0]
    have := w_dec this hw₁succ
    apply w₁_prop.2
    convert this
  use w₀
  intro w
  constructor
  · intro hw
    contrapose! hw
    apply hnotin
    assumption
  · exact hin w
