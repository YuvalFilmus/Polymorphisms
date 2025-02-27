import Polymorphisms.FinsetOrder
import Polymorphisms.SymmetricOnlyIfHelpers
open Finset

lemma sum_of_three {α β : Type} [DecidableEq α] [AddCommMonoid β]
  {A B C U : Finset α} (hU : U = A ∪ B ∪ C)
  (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
  (f : α → β) :
  ∑ i ∈ U, f i = ∑ i ∈ A, f i + ∑ i ∈ B, f i + ∑ i ∈ C, f i := calc
  ∑ i ∈ U, f i = ∑ i ∈ (A ∪ B), f i + ∑ i ∈ C, f i := by
    rw [hU]
    apply sum_union
    apply disjoint_union_left.mpr
    constructor <;> assumption
  _ = ∑ i ∈ A, f i + ∑ i ∈ B, f i + ∑ i ∈ C, f i := by
    congr
    apply sum_union
    assumption

instance (S : SymmetricB) : Inhabited (range S.m) :=
  ⟨range_0⟩

syntax "in_range" : tactic

macro_rules
  | `(tactic| in_range) => `(tactic| apply mem_range.mpr; omega)

-- open Lean Elab Tactic Term Meta in
-- elab_rules : tactic
-- | `(tactic| in_range) => do
--   evalTactic (← `(tactic| apply mem_range.mpr; omega))

set_option maxHeartbeats 300000
lemma nontrivial_if_has_monotone_counterexample {S}
  (h : has_monotone_counterexample (P_of_S S)) :
  is_nontrivial_S S := by
  obtain ⟨poly, hpoly, ⟨ic, hic⟩, x₀, nPx₀, hx₀0, hx₀1⟩ := h
  simp only [PredicateB_of_SymmetricB] at *
  -- break apart sums
  let A : Finset (range S.m) := { i | poly.fs i = C0 }
  let B : Finset (range S.m) := { i | poly.fs i = C1 }
  let C : Finset (range S.m) := { i | poly.fs i = ID }
  let U : Finset (range S.m) := univ
  have hAB_nonempty : #A + #B > 0 := by
    cases hic
    case inl h0 =>
      have : ic ∈ A := by simp [A]; assumption
      have : A.Nonempty := by use ic
      have : #A > 0 := card_pos.mpr this
      omega
    case inr h1 =>
      have : ic ∈ B := by simp [B]; assumption
      have : B.Nonempty := by use ic
      have : #B > 0 := card_pos.mpr this
      omega
  have hU : U = A ∪ B ∪ C := by
    apply ext
    intro i
    simp [U, A, B, C]
    apply hpoly i
  have hAB : Disjoint A B := by
    apply disjoint_iff_ne.mpr
    intro a ha b hb
    replace ha := (mem_filter.mp ha).2
    replace hb := (mem_filter.mp hb).2
    by_contra! h
    rw [h, hb] at ha
    contradiction
  have hAC : Disjoint A C := by
    apply disjoint_iff_ne.mpr
    intro a ha b hb
    replace ha := (mem_filter.mp ha).2
    replace hb := (mem_filter.mp hb).2
    by_contra! h
    rw [h, hb] at ha
    contradiction
  have hBC : Disjoint B C := by
    apply disjoint_iff_ne.mpr
    intro a ha b hb
    replace ha := (mem_filter.mp ha).2
    replace hb := (mem_filter.mp hb).2
    by_contra! h
    rw [h, hb] at ha
    contradiction
  have sum_sizes : #A + #B + #C = S.m := by
    rw [←card_disjUnion A B hAB]
    simp
    have : Disjoint (A ∪ B) C := by
      apply disjoint_union_left.mpr
      constructor <;> assumption
    rw [←card_disjUnion (A ∪ B) C this]
    simp
    rw [←union_assoc, ←hU, card_univ, ←card_univ]
    simp
  let wtA (x : range S.m → range 2) := ∑ i ∈ A, coe_vec x i
  let wtB (x : range S.m → range 2) := ∑ i ∈ B, coe_vec x i
  let wtC (x : range S.m → range 2) := ∑ i ∈ C, coe_vec x i
  have wt_sum (x : range S.m → range 2) : wt x = wtA x + wtB x + wtC x := by
    simp [wt, wtA, wtB, wtC]
    convert sum_of_three hU hAB hAC hBC (coe_vec x ·)
    simp [U]
    symm
    apply sum_attach
  -- containment in S.W given x ∈ P
  have wt_ub (x : range S.m → range 2) (D : Finset (range S.m)) :
    ∑ i ∈ D, coe_vec x i ≤ #D := calc
    ∑ i ∈ D, coe_vec x i ≤ ∑ i ∈ D, 1 := by
      apply sum_le_sum
      intro i hi
      replace hi : i < S.m := by
        apply mem_range.mp
        exact i.property
      simp [coe_vec, hi]
      have := mem_range.mp (x i).property
      omega
    _ = #D := by
      rw [sum_const]
      simp
  have wtC_ub (x : range S.m → range 2) : wtC x ≤ #C := wt_ub x C
  have W_given_P_ub (x : range S.m → range 2) : #B + wtC x ∈ range (S.m+1) := by
    apply mem_range.mpr
    have : wtC x ≤ #C := wtC_ub x
    omega
  have W_given_P {x : range S.m → range 2} (Px : (P_of_S S).P x) :
    ⟨#B + wtC x, W_given_P_ub x⟩ ∈ S.W := by
    let y i := poly.fs i (x i)
    have Py : (P_of_S S).P y := poly.app x Px
    have hA {i} (h : i ∈ A) : y i = b0 := by
      have : poly.fs i = C0 := (mem_filter.mp h).2
      simp [y, this, C0]
    have hB {i} (h : i ∈ B) : y i = b1 := by
      have : poly.fs i = C1 := (mem_filter.mp h).2
      simp [y, this, C1]
    have hC {i} (h : i ∈ C) : y i = x i := by
      have : poly.fs i = ID := (mem_filter.mp h).2
      simp [y, this, ID]
    have wtAy : wtA y = 0 := calc
      wtA y = ∑ i ∈ A, coe_vec y i := by simp [wtA]
      _ = ∑ i ∈ A, 0 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp i.property, hA hi, b0]
      _ = 0 := by apply sum_const_zero
    have wtBy : wtB y = #B := calc
      wtB y = ∑ i ∈ B, coe_vec y i := by simp [wtB]
      _ = ∑ i ∈ B, 1 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp i.property, hB hi, b1]
        exact mem_range.mp i.property
      _ = #B := by rw [sum_const]; simp
    have wtCy : wtC y = wtC x := calc
      wtC y = ∑ i ∈ C, coe_vec y i := by simp [wtC]
      _ = ∑ i ∈ C, coe_vec x i := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec]
        rw [hC hi]
        simp [PredicateB_of_SymmetricB]
      _ = wtC x := by simp [wtC]
    have wt_y : wt y = #B + wtC x := calc
      wt y = 0 + #B + wtC x := by
        rw [wt_sum y, wtAy, wtBy, wtCy]
      _ = #B + wtC x := by omega
    convert mem_symmetric_of_mem_predicate Py
    symm; assumption
  -- corollary: S.W contains some weight in [#B, #B+#C]
  have middle_interval_nonempty :
    ∃ w, w ∈ S.W ∧ #B ≤ w ∧ w ≤ #B + #C := by
    obtain ⟨x, Px, _⟩ := (P_of_S S).full range_0 b0
    let w : range (S.m+1) := ⟨#B + wtC x, W_given_P_ub x⟩
    have hw : w ∈ S.W := W_given_P Px
    use w
    constructor
    exact hw
    constructor
    simp [w]
    simp [w]
    apply wtC_ub
  -- S.W cannot contain all weights in [#B, #B+#C]
  have middle_interval_nonfull :
    ∃ w, w ∉ S.W ∧ #B ≤ w ∧ w ≤ #B + #C := by
    use wt x₀
    constructor
    exact nPx₀
    have hx₀A {i} (h : i ∈ A) : x₀ i = b0 := hx₀0 i (mem_filter.mp h).2
    have hx₀B {i} (h : i ∈ B) : x₀ i = b1 := hx₀1 i (mem_filter.mp h).2
    have wtAx₀ : wtA x₀ = 0 := calc
      wtA x₀ = ∑ i ∈ A, coe_vec x₀ i := by simp [wtA]
      _ = ∑ i ∈ A, 0 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp i.property, hx₀A hi, b0]
      _ = 0 := by apply sum_const_zero
    have wtBx₀ : wtB x₀ = #B := calc
      wtB x₀ = ∑ i ∈ B, coe_vec x₀ i := by simp [wtB]
      _ = ∑ i ∈ B, 1 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp i.property, hx₀B hi, b1]
        exact mem_range.mp i.property
      _ = #B := by rw [sum_const]; simp
    have hw : wt x₀ = #B + wtC x₀ := calc
      wt x₀ = 0 + #B + wtC x₀ := by
        rw [wt_sum x₀, wtAx₀, wtBx₀]
      _ = #B + wtC x₀ := by omega
    constructor
    · rw [hw]; omega
    · rw [hw]; have := wtC_ub x₀; omega
  -- showing that a weight belongs to S.W
  have W_condition {a b c : ℕ} (ha : a ≤ #A) (hb : b ≤ #B) (hc : c ≤ #C)
    (hw : ⟨a + b + c, by in_range⟩ ∈ S.W) :
    ⟨#B + c, by in_range⟩ ∈ S.W := by
    let w : range (S.m+1) := ⟨a + b + c, by apply mem_range.mpr; omega⟩
    replace hw : w ∈ S.W := hw
    let xA : range #A → range 2 := std_vec ⟨a, by apply mem_range.mpr; omega⟩
    let xB : range #B → range 2 := std_vec ⟨b, by apply mem_range.mpr; omega⟩
    let xC : range #C → range 2 := std_vec ⟨c, by apply mem_range.mpr; omega⟩
    let bijA := (finset_to_range_bij A).symm
    let bijB := (finset_to_range_bij B).symm
    let bijC := (finset_to_range_bij C).symm
    let x (i : range S.m) : range 2 :=
      if hA : i ∈ A then
        xA (bijA ⟨i, hA⟩)
      else if hB : i ∈ B then
        xB (bijB ⟨i, hB⟩)
      else if hC : i ∈ C then
        xC (bijC ⟨i, hC⟩)
      else -- never happens
        b0
    have wtAx : wtA x = a := calc
      wtA x = ∑ i ∈ A, coe_vec x i := by simp [wtA]
      _ = ∑ i ∈ range #A, coe_vec xA i := by
        let i (a : range S.m) (ha : a ∈ A) : ℕ := bijA.toFun ⟨a, ha⟩
        let j (a : ℕ) (ha : a ∈ range #A) : range S.m := bijA.invFun ⟨a, ha⟩
        have hi a ha : i a ha ∈ range #A := by simp [i]
        have hj a ha : j a ha ∈ A := by simp [j]
        have left_inv a ha : j (i a ha) (hi a ha) = a := by simp [i, j]
        have right_inv a ha : i (j a ha) (hj a ha) = a := by simp [i, j]
        let f (a : range S.m) := coe_vec x a
        let g (a : ℕ) := coe_vec xA a
        have h a ha : f a = g (i a ha) := by
          simp [f, g, coe_vec, x, ha, mem_range.mp (hi a ha), mem_range.mp a.2]
          congr
        exact sum_bij' i j hi hj left_inv right_inv h
      _ = wt xA := by simp [wt]
      _ = a := by simp [xA]
    have wtBx : wtB x = b := calc
      wtB x = ∑ i ∈ B, coe_vec x i := by simp [wtB]
      _ = ∑ i ∈ range #B, coe_vec xB i := by
        let i (a : range S.m) (ha : a ∈ B) : ℕ := bijB.toFun ⟨a, ha⟩
        let j (a : ℕ) (ha : a ∈ range #B) : range S.m := bijB.invFun ⟨a, ha⟩
        have hi a ha : i a ha ∈ range #B := by simp [i]
        have hj a ha : j a ha ∈ B := by simp [j]
        have left_inv a ha : j (i a ha) (hi a ha) = a := by simp [i, j]
        have right_inv a ha : i (j a ha) (hj a ha) = a := by simp [i, j]
        let f (a : range S.m) := coe_vec x a
        let g (a : ℕ) := coe_vec xB a
        have h a ha : f a = g (i a ha) := by
          have hA : a ∉ A := by
            by_contra! h
            contrapose! hAB
            apply not_disjoint_iff.mpr
            use a, h, ha
          simp [f, g, coe_vec, x, ha, mem_range.mp (hi a ha), mem_range.mp a.2, hA]
          congr
        exact sum_bij' i j hi hj left_inv right_inv h
      _ = wt xB := by simp [wt]
      _ = b := by simp [xB]
    have wtCx : wtC x = c := calc
      wtC x = ∑ i ∈ C, coe_vec x i := by simp [wtC]
      _ = ∑ i ∈ range #C, coe_vec xC i := by
        let i (a : range S.m) (ha : a ∈ C) : ℕ := bijC.toFun ⟨a, ha⟩
        let j (a : ℕ) (ha : a ∈ range #C) : range S.m := bijC.invFun ⟨a, ha⟩
        have hi a ha : i a ha ∈ range #C := by simp [i]
        have hj a ha : j a ha ∈ C := by simp [j]
        have left_inv a ha : j (i a ha) (hi a ha) = a := by simp [i, j]
        have right_inv a ha : i (j a ha) (hj a ha) = a := by simp [i, j]
        let f (a : range S.m) := coe_vec x a
        let g (a : ℕ) := coe_vec xC a
        have h a ha : f a = g (i a ha) := by
          have hA : a ∉ A := by
            by_contra! h
            contrapose! hAC
            apply not_disjoint_iff.mpr
            use a, h, ha
          have hB : a ∉ B := by
            by_contra! h
            contrapose! hBC
            apply not_disjoint_iff.mpr
            use a, h, ha
          simp [f, g, coe_vec, x, ha, mem_range.mp (hi a ha), mem_range.mp a.2, hA, hB]
          congr
        exact sum_bij' i j hi hj left_inv right_inv h
      _ = wt xC := by simp [wt]
      _ = c := by simp [xC]
    have wt_x : wt x = a + b + c := by
      rw [wt_sum, wtAx, wtBx, wtCx]
    have Px : (P_of_S S).P x := by
      simp [PredicateB_of_SymmetricB]
      convert hw
      simp [w]
      apply Subtype.coe_eq_of_eq_mk
      exact wt_x
    convert W_given_P Px
    rw [wtCx]
  -- main lemma (increase weight)
  have increase_weight {w : ℕ} (hB : #B > 0)
    (w_lb : #B ≤ w) (w_ub : w+1 ≤ #B+#C)
    (hw : ⟨w, by in_range⟩ ∈ S.W) :
    ⟨w+1, by in_range⟩ ∈ S.W := by
    let a : ℕ := 0
    let b : ℕ := #B - 1
    let c : ℕ := w - #B + 1
    have hw' : a+b+c = w := by omega
    have ha : a ≤ #A := by omega
    have hb : b ≤ #B := by omega
    have hc : c ≤ #C := by omega
    replace hw : ⟨a+b+c, by in_range⟩ ∈ S.W := by convert hw
    convert W_condition ha hb hc hw using 2
    omega
  -- main lemma (decrease weight)
  have decrease_weight {w : ℕ} (hA : #A > 0)
    (w_lb : #B ≤ w) (w_ub : w+1 ≤ #B+#C)
    (hw : ⟨w+1, by in_range⟩ ∈ S.W) :
    ⟨w, by in_range⟩ ∈ S.W := by
    let a : ℕ := 1
    let b : ℕ := #B
    let c : ℕ := w - #B
    have hw' : a+b+c = w+1 := by omega
    have ha : a ≤ #A := by omega
    have hb : b ≤ #B := by omega
    have hc : c ≤ #C := by omega
    replace hw : ⟨a+b+c, by in_range⟩ ∈ S.W := by convert hw
    convert W_condition ha hb hc hw using 2
    omega
  -- main lemma (iff version)
  have weight_iff {w : ℕ} (hA : #A > 0) (hB : #B > 0)
    (w_lb : #B ≤ w) (w_ub : w+1 ≤ #B+#C) :
    ⟨w, by in_range⟩ ∈ S.W ↔ ⟨w+1, by in_range⟩ ∈ S.W := by
    constructor
    · intro hw; apply increase_weight <;> assumption
    · intro hw; apply decrease_weight <;> assumption
  -- auxiliary lemma (#A = 0)
  have increase_weight' {w : ℕ} (w_ub : w ≤ #B)
    (hw : ⟨w, by in_range⟩ ∈ S.W) : ⟨#B, by in_range⟩ ∈ S.W := by
    let a : ℕ := 0
    let b : ℕ := w
    let c : ℕ := 0
    have hw' : a+b+c = w := by omega
    have ha : a ≤ #A := by omega
    have hb : b ≤ #B := by omega
    have hc : c ≤ #C := by omega
    replace hw : ⟨a+b+c, by in_range⟩ ∈ S.W := by convert hw
    convert W_condition ha hb hc hw using 2
  -- auxiliary lemma (#B = 0)
  have decrease_weight' {w : ℕ} (w_lb : #B + #C ≤ w) (w_ub : w ≤ S.m)
    (hw : ⟨w, by in_range⟩ ∈ S.W) : ⟨#B + #C, by in_range⟩ ∈ S.W := by
    let a : ℕ := w - (#B + #C)
    let b : ℕ := #B
    let c : ℕ := #C
    have hw' : a+b+c = w := by omega
    have ha : a ≤ #A := by omega
    have hb : b ≤ #B := by omega
    have hc : c ≤ #C := by omega
    replace hw : ⟨a+b+c, by in_range⟩ ∈ S.W := by convert hw
    convert W_condition ha hb hc hw using 2
  -- induction for #A, #B > 0
  have weight_iff' {w : ℕ} (hA : #A > 0) (hB : #B > 0)
    (w_lb : #B ≤ w) (w_ub : w ≤ #B+#C) :
    ⟨w, by in_range⟩ ∈ S.W ↔ ⟨#B, by in_range⟩ ∈ S.W := by
    revert w_lb w_ub
    induction w
    case zero => omega
    case succ w' hind =>
    by_cases w'+1 < #B
    case pos => intro _; omega
    case neg =>
    by_cases w'+1 = #B
    case pos h =>
      intro _ _
      conv => rhs; rhs; arg 1; rw [←h]
    case neg =>
    by_cases w'+1 > #B + #C
    case pos => intro _ _; omega
    case neg =>
    intro w'_lb w'_ub
    have w_lb : #B ≤ w' := by omega
    have w_ub : w'+1 ≤ #B + #C := by omega
    have hstep := weight_iff hA hB w_lb w_ub
    replace hind := hind w_lb (by omega)
    exact Iff.trans (Iff.symm hstep) hind
  -- induction for #A = 0
  have weight_if_up {w : ℕ} (hB : #B > 0) (hwB : ⟨#B, by in_range⟩ ∈ S.W)
    (w_lb : #B ≤ w) (w_ub : w ≤ #B+#C) : ⟨w, by in_range⟩ ∈ S.W := by
    revert w_lb w_ub
    induction w
    case zero => intro _; omega
    case succ w' hind =>
    by_cases w'+1 < #B
    case pos => intro _; omega
    case neg =>
    by_cases w'+1 = #B
    case pos =>
      intro _ _
      convert hwB
    by_cases #B+#C < w'+1
    case pos => intro _ _; omega
    case neg =>
      intro w_lb w_ub
      replace w_lb : #B ≤ w' := by omega
      apply increase_weight hB w_lb (by omega)
      apply hind w_lb (by omega)
  -- induction for #B = 0
  have weight_if_down' {w' : ℕ} (hA : #A > 0) (hwBC : ⟨#B+#C, by in_range⟩ ∈ S.W)
    (w'_nonneg : w' ≤ S.m) (w'_lb : #B ≤ S.m-w') (w'_ub : S.m-w' ≤ #B+#C) :
    ⟨S.m-w', by in_range⟩ ∈ S.W := by
    revert w'_lb w'_ub
    induction w'
    case zero => intro _; omega
    case succ w'' hind =>
    by_cases #B+#C < S.m-(w''+1)
    case pos => intro _; omega
    case neg =>
    by_cases #B+#C = S.m-(w''+1)
    case pos h =>
      intro _ _
      convert hwBC using 1
      apply Subtype.coe_eq_of_eq_mk
      simp
      rw [h]
    by_cases S.m-(w''+1) < #B
    case pos => intro _ _; omega
    case neg =>
      intro w'_lb w'_ub
      replace hind : ⟨S.m-w'', by in_range⟩ ∈ S.W := by
        apply hind <;> omega
      replace hind : ⟨S.m-w''-1+1, by in_range⟩ ∈ S.W := by
        convert hind using 1
        apply Subtype.coe_eq_of_eq_mk
        simp
        have : w'' < S.m := by omega
        omega
      convert decrease_weight hA (by omega) (by omega) hind using 1
  have weight_if_down {w : ℕ} (hA : #A > 0) (hwBC : ⟨#B+#C, by in_range⟩ ∈ S.W)
    (w_lb : #B ≤ w) (w_ub : w ≤ #B+#C) : ⟨w, by in_range⟩ ∈ S.W := by
    let w' := S.m - w
    have : ⟨S.m - w', by in_range⟩ ∈ S.W := weight_if_down' hA hwBC (by omega) (by omega) (by omega)
    convert this
    omega
  -- the case #A, #B > 0
  by_cases #A > 0 ∧ #B > 0
  case pos h =>
    obtain ⟨hA, hB⟩ := h
    obtain ⟨w₁, hw₁, w₁_lb, w₁_ub⟩ := middle_interval_nonempty
    obtain ⟨w₂, hw₂, w₂_lb, w₂_ub⟩ := middle_interval_nonfull
    have hw₁' := weight_iff' hA hB w₁_lb w₁_ub
    have hw₂' := weight_iff' hA hB w₂_lb w₂_ub
    exfalso
    exact hw₂ (hw₂'.mpr (hw₁'.mp hw₁))
  -- the case #A = 0
  case neg h =>
  have W_nonempty : S.W.Nonempty := by
    obtain ⟨w, hw, _, _⟩ := middle_interval_nonempty
    use w, hw
  by_cases #A = 0
  case pos hA =>
    have hB : #B > 0 := by omega
    have w_inc {w : range (S.m+1)} (w_ub : w.1 < S.m) (hw : w ∈ S.W) :
      ⟨w+1, by in_range⟩ ∈ S.W := by
      by_cases w ≤ #B
      case pos h =>
        have hwB := increase_weight' h hw
        obtain ⟨w₀, hw₀, w₀_lb, w₀_ub⟩ := middle_interval_nonfull
        have := weight_if_up hB hwB w₀_lb w₀_ub
        exfalso
        exact hw₀ this
      case neg h =>
        apply increase_weight hB <;> try omega
        exact hw
    obtain ⟨w₀, hw₀⟩ := w_inc_lemma W_nonempty w_inc
    exact construct_atleast hw₀
  -- the case #B = 0
  case neg h' =>
    have hA : #A > 0 := by omega
    have hB : #B = 0 := by omega
    have w_dec {w : range (S.m+1)} (w_lb : 0 < w.1) (hw : w ∈ S.W) :
      ⟨w-1, by apply mem_range.mpr; have := mem_range.mp w.property; omega⟩ ∈ S.W := by
      by_cases #B + #C ≤ w
      case pos h =>
        have w_ub : w ≤ S.m := by
          have := mem_range.mp w.property
          omega
        have hwBC := decrease_weight' h w_ub hw
        obtain ⟨w₀, hw₀, w₀_lb, w₀_ub⟩ := middle_interval_nonfull
        have := weight_if_down hA hwBC w₀_lb w₀_ub
        exfalso
        exact hw₀ this
      case neg h =>
        apply decrease_weight hA <;> try omega
        convert hw
        omega
    obtain ⟨w₀, hw₀⟩ := w_dec_lemma W_nonempty w_dec
    exact construct_atmost hw₀
