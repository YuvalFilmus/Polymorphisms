-- in this file we show that non-triviality implies a specific structure

import Polymorphisms.ExtendPartialInjection
import Polymorphisms.SymmetricOnlyIfHelpers
open Finset

lemma nontrivial_if_has_nonconst_counterexample' {S} {poly : Polymorphism₁B (P_of_S S)}
  (hnonconst : ∀ i, poly.fs i = ID ∨ poly.fs i = NEG)
  (hnontrivial : ∃ i, poly.fs i = NEG) :
  is_nontrivial_S S ∨
  (is_comp_closed S ∧ ∀ i, poly.fs i = NEG) := by
  -- take care of the trivial case first (all NEG)
  by_cases ∀ i, poly.fs i = NEG
  case pos h =>
    right
    constructor
    case h.right => exact h
    apply comp_closed
    intro w hw
    let v := std_vec w
    have Pv : (P_of_S S).P v := mem_std_vec.mpr hw
    let compv i := poly.fs i (v i)
    have Pcompv : (P_of_S S).P compv := poly.app v Pv
    convert mem_symmetric_of_mem_predicate Pcompv
    rw [←@wt_std_vec S.m w, ←wt_NEG_vec v]
    congr
    funext i
    simp [NEG_vec, compv, h i]
  -- show that XORing any two coordinates is a polymorphism
  case neg h =>
  push_neg at h
  left
  obtain ⟨iNEG, hiNEG⟩ := hnontrivial
  obtain ⟨iID, hiID⟩ := h
  have hi_diff : iNEG ≠ iID := by
    by_contra! h
    rw [←h] at hiID
    contradiction
  replace hiID : poly.fs iID = ID := by
    cases hnonconst iID
    case inl => assumption
    case inr => contradiction
  let poly' := permute_poly₁ (transposition iNEG iID) poly
  let poly'' : Polymorphism₁B (P_of_S S) :=
  {
    fs i σ := poly'.fs i (poly.fs i σ)
    app y Py := by
      apply poly'.app
      apply poly.app
      assumption
  }
  have hpoly''_NEG : poly''.fs iNEG = NEG ∧ poly''.fs iID = NEG := by
    symm at hi_diff
    simp [poly'', poly', permute_poly₁, transposition, hiNEG, hiID, hi_diff]
    constructor
    · funext b
      simp [ID, NEG]
    · funext b
      simp [ID, NEG]
  have hpoly''_ID {i} (hi₁ : i ≠ iNEG) (hi₂ : i ≠ iID) : poly''.fs i = ID := by
    simp [poly'', poly', permute_poly₁, transposition, hi₁, hi₂, hiNEG, hiID, hi_diff]
    funext b
    simp [ID]
    cases hnonconst i
    case inl h => rw [h]; simp [ID]
    case inr h => rw [h]; simp
  have XOR_two_poly {i j : range S.m} (h : i ≠ j) :
    ∃ poly : Polymorphism₁B (P_of_S S),
      ∀ (x : range S.m → range 2) (k : range S.m),
        poly.fs k (x k) = if k = i ∨ k = j then NEG (x k) else x k := by
    let e := perm_2_to_2 h hi_diff
    have he' : e = perm_2_to_2 h hi_diff := rfl
    have he := perm_2_to_2_spec h hi_diff
    rw [←he'] at he
    use permute_poly₁ e poly''
    intro x k
    simp [permute_poly₁]
    by_cases i = k
    case pos h => subst h; simp [he.1, hpoly''_NEG.1]
    case neg h =>
    by_cases j = k
    case pos h => subst h; simp [he.2, hpoly''_NEG.2]
    case neg h' =>
    replace h : k ≠ i := fun a ↦ h (id (Eq.symm a))
    replace h' : k ≠ j := fun a ↦ h' (id (Eq.symm a))
    simp [h, h']
    have hh : e k ≠ iNEG := by
      contrapose! h
      replace h : e k = iNEG := by tauto
      push_neg
      rw [←he.1] at h
      apply e.injective h
    have hh' : e k ≠ iID := by
      contrapose! h'
      replace h : e k = iID := by tauto
      push_neg
      rw [←he.2] at h
      apply e.injective h
    rw [hpoly''_ID hh hh']
    simp [ID]
  have can_XOR_two {i j : range S.m} (h : i ≠ j)
    {x} (Px : (P_of_S S).P x) :
    (P_of_S S).P (fun k ↦ if k = i ∨ k = j then NEG (x k) else x k) := by
    obtain ⟨poly, hpoly⟩ := XOR_two_poly h
    replace hpoly := hpoly x
    conv => arg 2; ext k; rw [←hpoly k]
    apply poly.app
    exact Px
  -- deduce the main property of the weights
  have hmain (w : ℕ) (hw : w ∈ range (S.m+1)) (hw2 : w+2 ∈ range (S.m+1)) :
    ⟨w, hw⟩ ∈ S.W ↔ ⟨w+2, hw2⟩ ∈ S.W := by
    have hm := symmetric_m_ge_2 S
    have := mem_range.mp hw2
    constructor
    · intro h
      let x := std_vec ⟨w, hw⟩
      have Px : (P_of_S S).P x := mem_std_vec.mpr h
      let i : range S.m := ⟨S.m-1, by apply mem_range.mpr; omega⟩
      let j : range S.m := ⟨S.m-2, by apply mem_range.mpr; omega⟩
      have hij : i ≠ j := by
        by_contra! h
        replace h : i.1 = j.1 := Subtype.eq_iff.mp h
        simp [i, j] at h
        omega
      have hi : x i = b0 := by
        simp [x, std_vec, b0, b1, i]
        omega
      have hj : x j = b0 := by
        simp [x, std_vec, b0, b1, j]
        omega
      let y (k : range S.m) := if k = i ∨ k = j then NEG (x k) else x k
      have Py : (P_of_S S).P y := can_XOR_two hij Px
      convert mem_symmetric_of_mem_predicate Py
      have hy : y = set_coord_to i b1 (set_coord_to j b1 x) := by
        funext k
        simp [y, set_coord_to]
        by_cases k = i
        case pos H =>
          simp [H, hi, NEG]
        case neg H =>
        by_cases k = j
        case pos H =>
          simp [H, hj, NEG]
        case neg H' =>
          simp [H, H']
      have hi' : (set_coord_to j b1 x) i = b0 := by
        simp [set_coord_to, hij, hi]
      simp [hy]
      rw [wt_0_to_1 hi', wt_0_to_1 hj]
      simp [x]
    · intro h
      let x := std_vec ⟨w+2, hw2⟩
      have Px : (P_of_S S).P x := mem_std_vec.mpr h
      let i : range S.m := range_0
      let j : range S.m := range_1
      have hij : i ≠ j := by simp [i, j, range_0, range_1]
      have hi : x i = b1 := by
        simp [x, std_vec, b0, b1, i, range_0]
      have hj : x j = b1 := by
        simp [x, std_vec, b0, b1, j, range_1]
      let y (k : range S.m) := if k = i ∨ k = j then NEG (x k) else x k
      have Py : (P_of_S S).P y := can_XOR_two hij Px
      convert mem_symmetric_of_mem_predicate Py
      have hy : y = set_coord_to i b0 (set_coord_to j b0 x) := by
        funext k
        simp [y, set_coord_to]
        by_cases k = i
        case pos H =>
          simp [H, hi, NEG]
        case neg H =>
        by_cases k = j
        case pos H =>
          simp [H, hj, NEG]
        case neg H' =>
          simp [H, H']
      have hi' : (set_coord_to j b0 x) i = b1 := by
        simp [set_coord_to, hij, hi]
      simp [hy]
      have := wt_1_to_0 hi'
      have := wt_1_to_0 hj
      have : (wt x).1 = w + 2 := by simp [x]
      omega
  -- deduce formula for weights
  have hmod2 (w : ℕ) : w % 2 ∈ range (S.m+1) := by
    have : w % 2 < 2 := by omega
    have : S.m ≥ 2 := symmetric_m_ge_2 S
    apply mem_range.mpr
    omega
  have hmain' (w : ℕ) (hw : w ∈ range (S.m+1)) :
    ⟨w, hw⟩ ∈ S.W ↔ ⟨w % 2, hmod2 w⟩ ∈ S.W := by
    induction' w using Nat.twoStepInduction with k IH IH'
    case zero => simp
    case one => simp
    case more =>
    simp
    have hk : k ∈ range (S.m+1) := by
      apply mem_range.mpr
      have := mem_range.mp hw
      omega
    have := IH hk
    have := hmain k hk hw
    tauto
  -- deduce the structure
  by_cases range_0 ∈ S.W
  case pos h0 =>
    simp [range_0] at h0
    by_cases range_1 ∈ S.W
    case pos h1 =>
      simp [range_1] at h1
      obtain ⟨w, hw⟩ := S.notfull
      replace hw : ⟨w % 2, hmod2 w⟩ ∉ S.W := by
        have := hmain' w.1 w.2
        tauto
      exfalso; apply hw
      mod_cases w.1 % 2
      · convert h0
      · convert h1
    case neg h1 =>
      simp [range_1] at h1
      left
      use S.m, symmetric_m_ge_2 S
      ext; rfl; simp [S_even]; apply Finset.ext_iff.mpr
      intro w; simp
      suffices ⟨w % 2, hmod2 w⟩ ∈ S.W ↔ w.1 % 2 = 0 by
        have := hmain' w.1 w.2
        have := @Nat.even_iff w.1
        tauto
      mod_cases w.1 % 2
      · unfold Nat.ModEq at H; simp [H]; assumption
      · unfold Nat.ModEq at H; simp [H]; assumption
  case neg h0 =>
    simp [range_0] at h0
    by_cases range_1 ∈ S.W
    case pos h1 =>
      simp [range_1] at h1
      right; left
      use S.m, symmetric_m_ge_2 S
      ext; rfl; simp [S_odd]; apply Finset.ext_iff.mpr
      intro w; simp
      suffices ⟨w % 2, hmod2 w⟩ ∈ S.W ↔ w.1 % 2 = 1 by
        have := hmain' w.1 w.2
        have := @Nat.odd_iff w.1
        tauto
      mod_cases w.1 % 2
      · unfold Nat.ModEq at H; simp [H]; assumption
      · unfold Nat.ModEq at H; simp [H]; assumption
    case neg h1 =>
      simp [range_1] at h1
      obtain ⟨w, hw, _⟩ := S.notall0
      replace hw : ⟨w % 2, hmod2 w⟩ ∈ S.W := by
        have := hmain' w.1 w.2
        tauto
      contrapose! hw
      mod_cases w.1 % 2
      · convert h0
      · convert h1

lemma nontrivial_if_has_nonconst_counterexample {S}
  (Φ : Set (formatB (P_of_S S))) (hID : (fun _ => ID) ∈ Φ)
  (h : has_nonconst_counterexample Φ) :
  is_nontrivial_S S ∨
  (is_comp_closed S ∧ ((fun _ => NEG) ∉ Φ)) := by
  obtain ⟨poly, hpoly, hΦ⟩ := h
  simp only [PredicateB_of_SymmetricB] at *
  by_cases ∃ i, poly.fs i = NEG
  case pos hnontrivial =>
    cases nontrivial_if_has_nonconst_counterexample' hpoly hnontrivial
    case inl h => left; exact h
    case inr h =>
      right
      constructor
      · exact h.1
      replace h := h.2
      contrapose! hΦ
      convert hΦ with i
      exact h i
  case neg htrivial =>
    push_neg at htrivial
    contrapose! hΦ
    convert hID with i
    cases hpoly i
    case inl h => exact h
    case inr h => have := htrivial i; contradiction

lemma nontrivial_if_has_closureB {S}
  (h : has_closureB (P_of_S S)) :
  is_nontrivial_S S := by
  obtain ⟨i₀, b, hclosed⟩ := h
  replace hclosed i : is_closed_underB (P_of_S S) i b := by
    by_cases i = i₀
    case pos h => subst h; assumption
    case neg h =>
    intro y Py
    let z := permute (transposition i i₀) y
    have Pz : (P_of_S S).P z := by apply predicate_symmetric ; assumption
    let w := set_coord_to i₀ b z
    have Pw : (P_of_S S).P w := hclosed z Pz
    suffices h : set_coord_to i b y = permute (transposition i i₀) w by
      rw [h]
      apply predicate_symmetric
      assumption
    funext k
    simp [set_coord_to, permute, transposition, w, z]
    by_cases k = i
    case pos hi =>
      by_cases k = i₀
      case pos hi₀ => simp [hi, hi₀]
      case neg hi₀ => simp [hi, hi₀]
    case neg hi =>
      by_cases k = i₀
      case pos hi₀ => simp [hi, hi₀, h]
      case neg hi₀ => simp [hi, hi₀]
  cases of_range_2B b
  case inl h =>
    subst h
    replace hclosed := hclosed range_0
    have w_dec {w : range (S.m+1)} (hw : 0 < w.1) (w_in : w ∈ S.W) :
      ⟨w-1, by apply mem_range.mpr; have := mem_range.mp w.property; omega⟩ ∈ S.W := by
      let x : range S.m → range 2 := std_vec w
      have Px : (P_of_S S).P x := mem_std_vec.mpr w_in
      have hx : x range_0 = b1 := by
        simp [x, std_vec, range_0, hw]
      let y := set_coord_to range_0 b0 x
      have Py : (P_of_S S).P y := hclosed x Px
      have wt_y : wt x = (wt y).1 + 1 := wt_1_to_0 hx
      simp [x] at wt_y
      convert mem_symmetric_of_mem_predicate Py
      omega
    have : S.W.Nonempty := by
      obtain ⟨w, w_in, _⟩ := S.notall0
      use w
    obtain ⟨w₀, hw₀⟩ := w_dec_lemma this w_dec
    apply construct_atmost hw₀
  case inr h =>
    subst h
    replace hclosed := hclosed range_l
    have w_inc {w : range (S.m+1)} (hw : w.1 < S.m) (w_in : w ∈ S.W) :
      ⟨w+1, by apply mem_range.mpr; omega⟩ ∈ S.W := by
      let x := std_vec w
      have Px : (P_of_S S).P x := mem_std_vec.mpr w_in
      have hx : x range_l = b0 := by
        simp [x, std_vec, range_l]
        omega
      let y := set_coord_to range_l b1 x
      have Py : (P_of_S S).P y := hclosed x Px
      have wt_y : wt y = (wt x).1 + 1 := wt_0_to_1 hx
      simp [x] at wt_y
      convert mem_symmetric_of_mem_predicate Py
      rw [wt_y]
    have : S.W.Nonempty := by
      obtain ⟨w, w_in, _⟩ := S.notall0
      use w
    obtain ⟨w₀, hw₀⟩ := w_inc_lemma this w_inc
    apply construct_atleast hw₀

def idempotent (f : (range 2 → range 2) → range 2) :=
  ∀ b : range 2, f (cons_input b b) = b

lemma AND_OR_idempotent {pred} (poly : PolymorphismB pred 2)
  (h : is_AND_OR_polyB poly) : ∀ i, idempotent (poly.fs i) := by
  intro i
  cases h i
  case inl hAND =>
    rw [hAND]
    intro b
    cases of_range_2B b <;> simp [AND, cons_input, range_0, range_1]
    case inl hb => simp [hb, b0, b1]
    case inr hb => simp [hb, b0, b1]
  case inr hOR =>
    rw [hOR]
    intro b
    cases of_range_2B b <;> simp [OR, cons_input, range_0, range_1]
    case inl hb => simp [hb, b0, b1]
    case inr hb => simp [hb, b0, b1]

lemma nontrivial_if_has_AND_OR_polyB_AND {S} {poly : PolymorphismB (P_of_S S) 2}
  (hANDOR : is_AND_OR_polyB poly)
  (hAND0 : poly.fs range_0 = AND)
  (hANDl : poly.fs range_l = AND) :
  is_nontrivial_S S := by
  have w_dec {w : range (S.m+1)} (hw₁ : 0 < w.1) (hw₂ : w.1 < S.m) (w_in : w ∈ S.W) :
    ⟨w-1, by apply mem_range.mpr; omega⟩ ∈ S.W := by
    let x := std_vec w
    have wt_x : wt x = w := by apply wt_std_vec
    have Px : (P_of_S S).P x := mem_std_vec.mpr w_in
    have hx₀ : x range_0 = b1 := by
      simp [x, std_vec, range_0, hw₁]
    have hx₁ : x range_l = b0 := by
      simp [x, std_vec, range_l]
      omega
    let y := permute (transposition range_0 range_l) x
    have Py : (P_of_S S).P y := by apply predicate_symmetric S x _ Px
    let xs i := cons_input (x i) (y i)
    let z i := poly.fs i (xs i)
    have Pz : (P_of_S S).P z := by
      apply poly.app xs
      intro j
      cases of_range_2 j
      case inl hj => subst hj; simp [xs, cons_input, range_0]; assumption
      case inr hj => subst hj; simp [xs, cons_input, range_0, range_1]; assumption
    have hz : z = set_coord_to range_0 b0 x := by
      funext i
      simp [set_coord_to, xs, z, y, permute, transposition]
      by_cases i = range_0
      case pos h =>
        simp [h, hx₀, hx₁, hAND0, AND, cons_input, b0, b1]
        simp [range_0, range_1, range_l, PredicateB_of_SymmetricB]
      case neg h =>
      by_cases i = range_l
      case pos h' =>
        simp [h, h', hx₀, hx₁, hANDl, AND, cons_input, b0, b1]
      case neg h' =>
        simp [h, h']
        apply AND_OR_idempotent poly hANDOR i
    have : wt x = (wt z).1 + 1 := by
      rw [hz]
      apply wt_1_to_0
      assumption
    convert mem_symmetric_of_mem_predicate Pz
    rw [wt_x] at this
    omega
  let W := S.W.erase range_l
  replace w_dec {w : range (S.m+1)} (hw₁ : 0 < w.1) (w_in : w ∈ W) :
    ⟨w-1, by apply mem_range.mpr; have := mem_range.mp w.property; omega⟩ ∈ W := by
    have := mem_range.mp w.property
    by_cases w = range_l
    case pos =>
      have := (mem_erase.mp w_in).1
      contradiction
    case neg h =>
      apply mem_erase.mpr
      constructor
      · simp [range_l]
        omega
      have : w.1 < S.m := by
        contrapose! h
        simp [range_l]
        apply Subtype.coe_eq_of_eq_mk
        omega
      exact w_dec hw₁ this (mem_erase.mp w_in).2
  have hW : W.Nonempty := by
    obtain ⟨w, w_in, hw⟩ := S.notall1
    use w
    apply mem_erase.mpr
    constructor
    · simp [range_0]
      by_contra! h
      replace h := Subtype.eq_iff.mp h
      simp [range_l] at h
      omega
    assumption
  obtain ⟨w₀, hw₀⟩ := w_dec_lemma hW w_dec
  by_cases range_l ∈ S.W
  case pos h0_in =>
    replace hw₀ (w : range (S.m+1)) : w ∈ S.W ↔ (w ≤ w₀ ∨ w = range_l) := by
      constructor
      · intro w_in
        by_cases w = range_l
        case pos hw =>
          right
          assumption
        case neg hw =>
          left
          apply (hw₀ w).mp
          apply mem_erase.mpr
          constructor <;> assumption
      · intro h
        cases h
        case inl w_in =>
          have : w ∈ W := (hw₀ w).mpr w_in
          exact (mem_erase.mp this).2
        case inr htriv =>
          rw [htriv]
          assumption
    apply construct_atmost_m hw₀
  case neg hl_out =>
    have : W = S.W := erase_eq_of_not_mem hl_out
    rw [this] at hw₀
    apply construct_atmost hw₀

lemma nontrivial_if_has_AND_OR_polyB_OR {S} {poly : PolymorphismB (P_of_S S) 2}
  (hANDOR : is_AND_OR_polyB poly)
  (hOR0 : poly.fs range_0 = OR)
  (hORl : poly.fs range_l = OR) :
  is_nontrivial_S S := by
  have w_inc {w : range (S.m+1)} (hw₁ : 0 < w.1) (hw₂ : w.1 < S.m) (w_in : w ∈ S.W) :
    ⟨w+1, by apply mem_range.mpr; omega⟩ ∈ S.W := by
    let x := std_vec w
    have wt_x : wt x = w := by apply wt_std_vec
    have Px : (P_of_S S).P x := mem_std_vec.mpr w_in
    have hx₀ : x range_0 = b1 := by
      simp [x, std_vec, range_0, hw₁]
    have hx₁ : x range_l = b0 := by
      simp [x, std_vec, range_l]
      omega
    let y := permute (transposition range_0 range_l) x
    have Py : (P_of_S S).P y := by apply predicate_symmetric S x _ Px
    let xs i := cons_input (x i) (y i)
    let z i := poly.fs i (xs i)
    have Pz : (P_of_S S).P z := by
      apply poly.app xs
      intro j
      cases of_range_2 j
      case inl hj => subst hj; simp [xs, cons_input, range_0]; assumption
      case inr hj => subst hj; simp [xs, cons_input, range_0, range_1]; assumption
    have hz : z = set_coord_to range_l b1 x := by
      funext i
      simp [set_coord_to, xs, z, y, permute, transposition]
      by_cases i = range_0
      case pos h =>
        simp [h, hx₀, hx₁, hOR0, OR, cons_input, b0, b1]
      case neg h =>
      by_cases i = range_l
      case pos h' =>
        simp [h, h', hx₀, hx₁, hORl, OR, cons_input, b0, b1]
        simp [range_0, range_1, range_l, PredicateB_of_SymmetricB]
        split
        case _ => omega
        case _ => simp [range_0] at hx₀; rw [hx₀]; simp [b1]
      case neg h' =>
        simp [h, h']
        apply AND_OR_idempotent poly hANDOR i
    have : wt z = (wt x).1 + 1 := by
      rw [hz]
      apply wt_0_to_1
      assumption
    convert mem_symmetric_of_mem_predicate Pz
    rw [this, wt_x]
  let W := S.W.erase range_0
  replace w_inc {w : range (S.m+1)} (hw₂ : w.1 < S.m) (w_in : w ∈ W) :
    ⟨w+1, by apply mem_range.mpr; omega⟩ ∈ W := by
    by_cases w = range_0
    case pos =>
      have := (mem_erase.mp w_in).1
      contradiction
    case neg h =>
      apply mem_erase.mpr
      constructor
      · simp [range_0]
      have : 0 < w.1 := by
        contrapose! h
        simp [range_0]
        apply Subtype.coe_eq_of_eq_mk
        omega
      exact w_inc this hw₂ (mem_erase.mp w_in).2
  have hW : W.Nonempty := by
    obtain ⟨w, w_in, hw⟩ := S.notall0
    use w
    apply mem_erase.mpr
    constructor
    · simp [range_0]; by_contra! h; replace h := Subtype.eq_iff.mp h; simp at h; omega
    assumption
  obtain ⟨w₀, hw₀⟩ := w_inc_lemma hW w_inc
  by_cases range_0 ∈ S.W
  case pos h0_in =>
    replace hw₀ (w : range (S.m+1)) : w ∈ S.W ↔ (w₀ ≤ w ∨ w = range_0) := by
      constructor
      · intro w_in
        by_cases w = range_0
        case pos hw =>
          right
          assumption
        case neg hw =>
          left
          apply (hw₀ w).mp
          apply mem_erase.mpr
          constructor <;> assumption
      · intro h
        cases h
        case inl w_in =>
          have : w ∈ W := (hw₀ w).mpr w_in
          exact (mem_erase.mp this).2
        case inr htriv =>
          rw [htriv]
          assumption
    apply construct_atleast_0 hw₀
  case neg h0_out =>
    have : W = S.W := erase_eq_of_not_mem h0_out
    rw [this] at hw₀
    apply construct_atleast hw₀

lemma is_AND_OR_conserved {S}
  {poly : PolymorphismB (P_of_S S) 2} (hpoly : is_AND_OR_polyB poly)
  (e : Equiv.Perm (range S.m)) :
  is_AND_OR_polyB (permute_poly e poly) := by
  intro i
  simp [permute_poly]
  exact hpoly (e i)

lemma nontrivial_if_has_AND_OR_polyB {S}
  (h : has_AND_OR_polyB (P_of_S S)) :
  is_nontrivial_S S := by
  obtain ⟨poly, hpoly⟩ := h
  unfold is_AND_OR_polyB at hpoly
  simp only [PredicateB_of_SymmetricB] at hpoly
  cases m_ge_3_or_nontrivial S
  case inr h => exact h
  case inl hm =>
  cases hpoly range_0
  case inl hAND0 =>
    cases hpoly range_l
    case inl hANDl =>
      apply nontrivial_if_has_AND_OR_polyB_AND hpoly <;> assumption
    case inr hORl =>
      cases hpoly range_1
      case inl hAND1 =>
        let e : Equiv.Perm (range S.m) := transposition range_1 range_l
        let poly' := permute_poly e poly
        apply nontrivial_if_has_AND_OR_polyB_AND (is_AND_OR_conserved hpoly e)
        · simp [permute_poly, e, transposition, range_0, range_1, range_l]
          split
          case _ => omega
          case _ => exact hAND0
        · simp [permute_poly, e, transposition, range_0, range_1, range_l, PredicateB_of_SymmetricB]
          split
          case _ => omega
          case _ => exact hAND1
      case inr hOR1 =>
        let e : Equiv.Perm (range S.m) := transposition range_0 range_1
        let poly' := permute_poly e poly
        apply nontrivial_if_has_AND_OR_polyB_OR (is_AND_OR_conserved hpoly e)
        · simp [permute_poly, e, transposition, range_0, range_1, range_l]
          exact hOR1
        · simp [permute_poly, e, transposition, range_0, range_1, range_l, PredicateB_of_SymmetricB]
          split
          case _ => omega
          case _ =>
          split
          case _ => omega
          case _ => exact hORl
  case inr hOR0 =>
    cases hpoly range_l
    case inr hORl =>
      apply nontrivial_if_has_AND_OR_polyB_OR <;> assumption
    case inl hANDl =>
      cases hpoly range_1
      case inl hAND1 =>
        let e : Equiv.Perm (range S.m) := transposition range_0 range_1
        let poly' := permute_poly e poly
        apply nontrivial_if_has_AND_OR_polyB_AND (is_AND_OR_conserved hpoly e)
        · simp [permute_poly, e, transposition, range_0, range_1, range_l]
          exact hAND1
        · simp [permute_poly, e, transposition, range_0, range_1, range_l, PredicateB_of_SymmetricB]
          split
          case _ => omega
          case _ =>
          split
          case _ => omega
          case _ => exact hANDl
      case inr hOR1 =>
        let e : Equiv.Perm (range S.m) := transposition range_1 range_l
        let poly' := permute_poly e poly
        apply nontrivial_if_has_AND_OR_polyB_OR (is_AND_OR_conserved hpoly e)
        · simp [permute_poly, e, transposition, range_0, range_1, range_l]
          split
          case _ => omega
          case _ => exact hOR0
        · simp [permute_poly, e, transposition, range_0, range_1, range_l, PredicateB_of_SymmetricB]
          split
          case _ => omega
          case _ => exact hOR1

lemma diff_of_atleast_3 {m} (hm : m ≥ 3) (i₀ i₁ : range m) :
  ∃ i₂ : range m, i₂ ≠ i₀ ∧ i₂ ≠ i₁ := by
  let r0 : range m := ⟨0, by apply mem_range.mpr; omega⟩
  let r1 : range m := ⟨1, by apply mem_range.mpr; omega⟩
  let r2 : range m := ⟨2, by apply mem_range.mpr; omega⟩
  use
    if i₀ = r0 then
      if i₁ = r0 then
        r1
      else if i₁ = r1 then
        r2
      else
        r1
    else if i₀ = r1 then
      if i₁ = r0 then
        r2
      else
        r0
    else if i₁ = r0 then
      r1
    else
      r0
  constructor
  · split
    case isTrue h =>
      split
      case isTrue h' =>
        simp [h, r0, r1]
      case isFalse h' =>
        simp [h]
        split <;> simp [r0, r1, r2]
    case isFalse h =>
      split
      case isTrue h' =>
        rw [h']
        split <;> simp [r0, r1, r2]
      case isFalse h' =>
        split <;> (symm; assumption)
  · split
    case isTrue h =>
      split
      case isTrue h' =>
        simp [h', r0, r1]
      case isFalse h' =>
        split
        case isTrue h'' => simp [h'', r1, r2]
        case isFalse h'' => symm; assumption
    case isFalse h =>
      split
      case isTrue h' =>
        split
        case isTrue h'' => simp [h'', r0, r2]
        case isFalse h'' => symm; assumption
      case isFalse h' =>
        split
        case isTrue h'' => simp [h'', r0, r1]
        case isFalse h'' => symm; assumption

lemma nontrivial_if_has_Latin_square_polyB {S Φ} (hperm : permutationalB Φ)
  (h : has_Latin_square_polyB (P_of_S S) Φ) :
  is_nontrivial_S S := by
  obtain ⟨poly, hpoly⟩ := h
  replace hpoly := is_Latin_square_of_is_Latin_square_polyB hperm hpoly
  replace hpoly i := is_XOR_of_is_Latin_square (hpoly i)
  simp only [PredicateB_of_SymmetricB] at hpoly
  let v (i : range S.m) : range 2 := if poly.fs i = XOR then b0 else b1
  have hv' (i : range S.m) a b : poly.fs i (cons_input a b) =
    XOR (cons_input a (XOR (cons_input b (v i)))) := by
    by_cases poly.fs i = XOR
    case pos h =>
      simp [h, v]
      cases of_range_2B a <;> cases of_range_2B b <;>
        simp [XOR, cons_input, range_0, range_1, b0, b1, *]
    case neg h =>
      simp [h, v]
      replace h : poly.fs i = XNOR := by
        have := hpoly i
        tauto
      cases of_range_2B a <;> cases of_range_2B b <;>
        simp [XOR, XNOR, cons_input, range_0, range_1, b0, b1, *]
  have hv (i : range S.m) x : poly.fs i x =
    XOR (cons_input (x range_0) (XOR (cons_input (x range_1) (v i)))) := by
    rw [←hv']
    congr
    simp
  have Pv : (P_of_S S).P v := by
    obtain ⟨x, Px, _⟩ := (P_of_S S).full range_0 b0
    let xs (i : range S.m) (_ : range 2) := x i
    have hvfs i : v i = poly.fs i (xs i) := by
      rw [hv i]
      simp [xs]
      cases of_range_2B (x i) <;> cases of_range_2B (v i) <;>
        simp [XOR, cons_input, range_0, range_1, b0, b1, *]
    suffices h : (P_of_S S).P (fun i ↦ v i) from h
    conv => arg 2; ext i; rw [hvfs i]
    apply poly.app xs
    intro j
    simp [xs]
    apply Px
  cases nontrivial_weight_or_nontrivial S
  case inr h => exact h
  case inl h =>
  obtain ⟨w₀, hw₀⟩ := h
  cases m_ge_3_or_nontrivial S
  case inr h => exact h
  case inl hm =>
  have : ∃ u : range S.m → range 2, (P_of_S S).P u ∧ u ≠ v ∧ u ≠ NEG_vec v := by
    by_cases (wt v).1 = 0 ∨ (wt v).1 = S.m
    case pos h =>
      use std_vec w₀
      constructor
      · apply mem_std_vec.mpr hw₀.1
      have hwt : (wt (std_vec w₀)).1 = w₀ := by simp
      cases h
      case inl h =>
        constructor
        · contrapose! hwt
          rw [hwt, h]
          omega
        · contrapose! hwt
          rw [hwt, wt_NEG_vec]
          simp [comp]
          omega
      case inr h =>
        constructor
        · contrapose! hwt
          rw [hwt, h]
          omega
        · contrapose! hwt
          rw [hwt, wt_NEG_vec]
          simp [comp]
          omega
    case neg h =>
      push_neg at h
      have : ∃ i, v i = b0 := by
        replace h := h.2
        contrapose! h
        replace h i : v i = b1 := b1_of_not_b0 (h i)
        have := wt_m.mpr h
        rw [this]
      obtain ⟨i₀, hi₀⟩ := this
      have : ∃ i, v i = b1 := by
        replace h := h.1
        contrapose! h
        replace h i : v i = b0 := b0_of_not_b1 (h i)
        have := wt_0.mpr h
        rw [this]
      obtain ⟨i₁, hi₁⟩ := this
      obtain ⟨i₂, hi₂⟩ := diff_of_atleast_3 hm i₀ i₁
      use permute (transposition i₀ i₁) v
      constructor
      · apply predicate_symmetric; assumption
      constructor
      · by_contra! heq
        have := congrFun heq i₀
        simp [permute, transposition, hi₀, hi₁, b0, b1] at this
      · by_contra! heq
        have := congrFun heq i₂
        simp [permute, transposition, hi₂, NEG_vec] at this
        contrapose! this
        apply NEG_ne
  obtain ⟨w, Pw, hw₀, hw₁⟩ := this
  have : ∃ i, v i ≠ w i := by
    contrapose! hw₀
    funext i
    rw [hw₀ i]
  obtain ⟨i₀, hi₀⟩ := this
  have : ∃ i, v i = w i := by
    contrapose! hw₁
    funext i
    simp [NEG_vec]
    rw [NEG_of_ne (hw₁ i)]
    simp
  obtain ⟨i₁, hi₁⟩ := this
  let e : Polymorphism₁B (P_of_S S) :=
  {
    fs i σ := poly.fs i (cons_input σ (w i))
    app y Py := by
      conv =>
        arg 2
        simp
      apply poly.app
      intro j
      cases of_range_2 j
      case inl hj =>
        simp [hj, cons_input]
        exact Py
      case inr hj =>
        simp [hj, cons_input, range_0, range_1]
        exact Pw
  }
  have he0 i (h : v i = w i) : e.fs i = ID := by
    funext σ
    simp [e]
    rw [hv' i]
    rw [h]
    cases of_range_2B σ <;> cases of_range_2B (w i) <;>
      simp [XOR, ID, cons_input, range_0, range_1, *, b0, b1]
  have he1 i (h : v i ≠ w i) : e.fs i = NEG := by
    funext σ
    simp [e]
    rw [hv' i]
    have := NEG_of_ne h
    rw [this]
    cases of_range_2B σ <;> cases of_range_2B (w i) <;>
      simp [XOR, NEG, cons_input, range_0, range_1, *, b0, b1]
  have hnonconst i : e.fs i = ID ∨ e.fs i = NEG := by
    by_cases v i = w i
    case pos h =>
      left
      exact he0 i h
    case neg h =>
      right
      exact he1 i h
  have hnontrivial : ∃ i, e.fs i = NEG := by
    use i₀
    exact he1 i₀ hi₀
  cases nontrivial_if_has_nonconst_counterexample' hnonconst hnontrivial
  case inl h => assumption
  case inr h =>
    exfalso
    have hNEG := h.2 i₁
    have hID := he0 i₁ hi₁
    rw [hNEG] at hID
    tauto
