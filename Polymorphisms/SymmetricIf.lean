-- in this file we prove the non-triviality of symmetric predicates

import Polymorphisms.Boolean
import Polymorphisms.SymmetricDefs
open Finset

def f_nonconst {n} (f : (range n → range 2) → range 2) :=
  ∃ x y, f x ≠ f y

def poly_nonconst {pred n} (poly : PolymorphismB pred n) :=
  ∀ i, f_nonconst (poly.fs i)

lemma not_certificate_of_nonconst {pred n} {poly : PolymorphismB pred n}
  (h : poly_nonconst poly) :
  ¬ is_certificateB poly := by
  by_contra! hcert
  obtain ⟨c, hc⟩ := hcert
  obtain ⟨i, hi⟩ := dom_nonemptyB c
  obtain ⟨x, y, hxy⟩ := h i
  apply hxy
  have hx := hc ⟨i, hi⟩ x
  have hy := hc ⟨i, hi⟩ y
  rw [hx, hy]

def f_dep {n} (f : (range n → range 2) → range 2) :=
  ∀ j, ∃ x y, f x ≠ f y ∧ x j = y j

def poly_dep {pred n} (poly : PolymorphismB pred n) :=
  ∃ i, f_dep (poly.fs i)

lemma not_dictator_of_dep {pred Φ n} {poly : PolymorphismB pred n}
  (h : poly_dep poly) :
  ¬ is_dictatorshipB poly Φ := by
  by_contra! hdict
  obtain ⟨j, φ, hφ, hfs⟩ := hdict
  obtain ⟨i, hdep⟩ := h
  obtain ⟨x, y, hf, hxy⟩ := hdep j
  apply hf
  rw [hfs i x, hfs i y, hxy]

def XOR₃ (x : range 3 → range 2) : range 2 :=
  XOR (cons_input (XOR (cons_input (x range_0) (x range_1))) (x range_2))

lemma nonconst_XOR₃ : f_nonconst XOR₃ := by
  use (fun _ ↦ b0), (fun _ ↦ b1)
  simp [XOR₃, XOR, cons_input, b0, b1, range_0, range_1]

def cons₃ (a b c : range 2) (j : range 3) : range 2 :=
  if j.1 = 0 then a else if j.1 = 1 then b else c

lemma dep_XOR₃ : f_dep XOR₃ := by
  intro j
  match hj : j.1 with
  | 0 =>
    use cons₃ b0 b0 b0, cons₃ b0 b0 b1
    simp [XOR₃, cons₃, XOR, cons_input, b0, b1, range_0, range_1, range_2, hj]
  | 1 =>
    use cons₃ b0 b0 b0, cons₃ b0 b0 b1
    simp [XOR₃, cons₃, XOR, cons_input, b0, b1, range_0, range_1, range_2, hj]
  | 2 =>
    use cons₃ b0 b0 b0, cons₃ b1 b0 b0
    simp [XOR₃, cons₃, XOR, cons_input, b0, b1, range_0, range_1, range_2, hj]
  | n+3 =>
    have := mem_range.mp j.property
    omega

lemma XOR₃_mod' (a b c : range 2) :
  XOR₃ (cons₃ a b c) ≡ a + b + c [MOD 2] := by
  cases of_range_2B a <;> cases of_range_2B b <;> cases of_range_2B c <;>
  (simp [XOR₃, XOR, cons₃, cons_input, b0, b1, range_0, range_1, range_2, *]; rfl)

lemma XOR₃_mod (x : range 3 → range 2) :
  XOR₃ x ≡ x range_0 + x range_1 + x range_2 [MOD 2] := by
  convert XOR₃_mod' (x range_0) (x range_1) (x range_2)
  funext i
  simp [cons₃, range_0, range_1, range_2]
  match hi : i.1 with
  | 0 => aesop
  | 1 => aesop
  | 2 => aesop
  | n+3 => have := mem_range.mp i.property; omega

lemma XOR₃_mod_vec {m} (xs : range m → range 3 → range 2) :
  wt (fun i ↦ XOR₃ (xs i)) ≡ (wt (xs · range_0) % 2) + (wt (xs · range_1) % 2) + (wt (xs · range_2) % 2) [MOD 2] := by
  have hwt j : ∑ i ∈ range m, (coe_vec (xs · j) i) % 2 ≡ wt (xs · j) [MOD 2] := calc
    ∑ i ∈ range m, (coe_vec (xs · j) i) % 2 ≡ ∑ i ∈ range m, coe_vec (xs · j) i [MOD 2] := by
      unfold Nat.ModEq
      rw [←sum_nat_mod]
    _ ≡ wt (xs · j) [MOD 2] := by
      unfold Nat.ModEq
      simp [wt]
  have h := calc
    ∑ i ∈ range m, (coe_vec (xs · range_0) i + coe_vec (xs · range_1) i) % 2 ≡
    ∑ i ∈ range m, ((coe_vec (xs · range_0) i) % 2 + (coe_vec (xs · range_1) i) % 2) % 2 [MOD 2] := by
      congr
      funext i
      rw [Nat.add_mod]
    _ ≡ ∑ i ∈ range m, ((coe_vec (xs · range_0) i) % 2 + (coe_vec (xs · range_1) i) % 2) [MOD 2] := by
      unfold Nat.ModEq
      rw [←sum_nat_mod]
    _ ≡ ∑ i ∈ range m, (coe_vec (xs · range_0) i) % 2 + ∑ i ∈ range m, (coe_vec (xs · range_1) i) % 2 [MOD 2] := by
      unfold Nat.ModEq
      congr
      rw [←sum_add_distrib]
    _ ≡ (∑ i ∈ range m, (coe_vec (xs · range_0) i) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_1) i) % 2) % 2 [MOD 2] := by
      unfold Nat.ModEq
      rw [Nat.add_mod]
  calc
  wt (fun i ↦ XOR₃ (xs i)) ≡ ∑ i ∈ range m, coe_vec (fun i ↦ XOR₃ (xs i)) i [MOD 2] := by
    simp [wt]
    rfl
  _ ≡ ∑ i ∈ range m, (coe_vec (fun i ↦ XOR₃ (xs i)) i) % 2 [MOD 2] := by
    unfold Nat.ModEq
    rw [sum_nat_mod]
   _ ≡ ∑ i ∈ range m, (coe_vec (xs · range_0) i + coe_vec (xs · range_1) i + coe_vec (xs · range_2) i) % 2 [MOD 2] := by
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [coe_vec, mem_range.mp hi]
    apply XOR₃_mod
  _ ≡ ∑ i ∈ range m, ((coe_vec (xs · range_0) i + coe_vec (xs · range_1) i) % 2 + (coe_vec (xs · range_2) i) % 2) % 2 [MOD 2] := by
    congr
    funext i
    rw [Nat.add_mod]
  _ ≡ ∑ i ∈ range m, ((coe_vec (xs · range_0) i + coe_vec (xs · range_1) i) % 2 + (coe_vec (xs · range_2) i) % 2) [MOD 2] := by
    unfold Nat.ModEq
    rw [←sum_nat_mod]
  _ ≡ ∑ i ∈ range m, (coe_vec (xs · range_0) i + coe_vec (xs · range_1) i) % 2 +
      ∑ i ∈ range m, (coe_vec (xs · range_2) i) % 2 [MOD 2] := by
    unfold Nat.ModEq
    congr
    rw [←sum_add_distrib]
  _ ≡ (∑ i ∈ range m, (coe_vec (xs · range_0) i + coe_vec (xs · range_1) i) % 2) % 2 +
      (∑ i ∈ range m, (coe_vec (xs · range_2) i) % 2) % 2 [MOD 2] := by
    unfold Nat.ModEq
    rw [Nat.add_mod]
  _ ≡ ((∑ i ∈ range m, (coe_vec (xs · range_0) i) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_1) i) % 2) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_2) i) % 2) % 2 [MOD 2] := by
    rw [h]
  _ ≡ ((∑ i ∈ range m, (coe_vec (xs · range_0) i) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_1) i) % 2) % 2) % 2 + ((∑ i ∈ range m, (coe_vec (xs · range_2) i) % 2) % 2) % 2 [MOD 2] := by
    congr 2
    rw [Nat.mod_mod]
  _ ≡ (∑ i ∈ range m, (coe_vec (xs · range_0) i) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_1) i) % 2) % 2 + (∑ i ∈ range m, (coe_vec (xs · range_2) i) % 2) % 2 [MOD 2] := by
    unfold Nat.ModEq
    rw [←Nat.add_mod]
  _ ≡ (wt (xs · range_0)) % 2 + (wt (xs · range_1)) % 2 + (wt (xs · range_2)) % 2 [MOD 2] := by
    rw [hwt range_0, hwt range_1, hwt range_2]

lemma S_even_nontrivial {m : ℕ} (hm : m ≥ 2) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_even hm)) Φ n := by
  unfold trivial_forB
  push_neg
  use 3, {
    fs _ := XOR₃
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_even]
      conv at sat =>
        ext j
        simp [PredicateB_of_SymmetricB, S_even]
      apply Nat.even_iff.mpr
      rw [XOR₃_mod_vec]
      conv =>
        left
        enter [1, 1, 1]
        tactic =>
          apply Nat.even_iff.mp
          convert sat range_0
      conv =>
        left
        enter [1, 1, 2]
        tactic =>
          apply Nat.even_iff.mp
          convert sat range_1
      conv =>
        left
        enter [1, 2]
        tactic =>
          apply Nat.even_iff.mp
          convert sat range_2
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_XOR₃
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_XOR₃

lemma S_odd_nontrivial {m : ℕ} (hm : m ≥ 2) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_odd hm)) Φ n := by
  unfold trivial_forB
  push_neg
  use 3, {
    fs _ := XOR₃
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_odd]
      conv at sat =>
        ext j
        simp [PredicateB_of_SymmetricB, S_odd]
      apply Nat.odd_iff.mpr
      rw [XOR₃_mod_vec]
      conv =>
        left
        enter [1, 1, 1]
        tactic =>
          apply Nat.odd_iff.mp
          convert sat range_0
      conv =>
        left
        enter [1, 1, 2]
        tactic =>
          apply Nat.odd_iff.mp
          convert sat range_1
      conv =>
        left
        enter [1, 2]
        tactic =>
          apply Nat.odd_iff.mp
          convert sat range_2
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_XOR₃
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_XOR₃

lemma nonconst_AND : f_nonconst AND := by
  use cons_input b0 b0, cons_input b1 b1
  simp [AND, cons_input, b0, b1]

lemma nonconst_OR : f_nonconst OR := by
  use cons_input b0 b0, cons_input b1 b1
  simp [OR, cons_input, b0, b1]

lemma dep_AND : f_dep AND := by
  intro j
  cases of_range_2 j
  case inl hj =>
    subst hj
    use cons_input b1 b1, cons_input b1 b0
    simp [AND, cons_input, b0, b1, range_0, range_1]
  case inr hj =>
    subst hj
    use cons_input b1 b1, cons_input b0 b1
    simp [AND, cons_input, b0, b1, range_0, range_1]

lemma dep_OR : f_dep OR := by
  intro j
  cases of_range_2 j
  case inl hj =>
    subst hj
    use cons_input b0 b0, cons_input b0 b1
    simp [OR, cons_input, b0, b1, range_0, range_1]
  case inr hj =>
    subst hj
    use cons_input b0 b0, cons_input b1 b0
    simp [OR, cons_input, b0, b1, range_0, range_1]

lemma wt_AND {m} (xs : range m → range 2 → range 2) :
  wt (fun i ↦ AND (xs i)) ≤ wt (xs · range_0) := calc
  wt (fun i ↦ AND (xs i)) = ∑ i ∈ range m, coe_vec (fun i ↦ AND (xs i)) i := by
    simp [wt]
  _ ≤ ∑ i ∈ range m, coe_vec (xs · range_0) i := by
    apply sum_le_sum
    intro i hi
    simp [coe_vec, mem_range.mp hi, AND]
    split
    case isTrue h =>
      rw [h.1]
    case isFalse h =>
      apply Subtype.coe_le_coe.mp
      simp [b0]
  _ = wt (xs · range_0) := by
    simp [wt]

lemma wt_OR {m} (xs : range m → range 2 → range 2) :
  wt (fun i ↦ OR (xs i)) ≥ wt (xs · range_0) := calc
  wt (fun i ↦ OR (xs i)) = ∑ i ∈ range m, coe_vec (fun i ↦ OR (xs i)) i := by
    simp [wt]
  _ ≥ ∑ i ∈ range m, coe_vec (xs · range_0) i := by
    apply sum_le_sum
    intro i hi
    simp [coe_vec, mem_range.mp hi, OR]
    split
    case isTrue h =>
      rw [h.1]
    case isFalse h =>
      apply Subtype.coe_le_coe.mp
      simp [b1]
      have := mem_range.mp (xs ⟨i, hi⟩ range_0).property
      omega
  _ = wt (xs · range_0) := by
    simp [wt]

lemma S_atmost_nontrivial {m b : ℕ} (hlb : 0 < b) (hub : b < m) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_atmost hlb hub)) Φ n := by
  unfold trivial_forB
  push_neg
  use 2, {
    fs _ := AND
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_atmost]
      calc
        ↑(wt (fun i ↦ AND (xs i))) ≤ ↑(wt (xs · range_0)) := wt_AND xs
        _ ≤ b := by
          have := sat range_0
          simp [PredicateB_of_SymmetricB, S_atmost] at this
          assumption
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_AND
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_AND

lemma S_atleast_nontrivial {m b : ℕ} (hlb : 0 < b) (hub : b < m) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_atleast hlb hub)) Φ n := by
  unfold trivial_forB
  push_neg
  use 2, {
    fs _ := OR
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_atleast]
      calc
        ↑(wt (fun i ↦ OR (xs i))) ≥ ↑(wt (xs · range_0)) := wt_OR xs
        _ ≥ b := by
          have := sat range_0
          simp [PredicateB_of_SymmetricB, S_atleast] at this
          assumption
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_OR
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_OR

lemma S_atmost_m_nontrivial {m b : ℕ} (hub : b+1 < m) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_atmost_m hub)) Φ n := by
  unfold trivial_forB
  push_neg
  use 2, {
    fs _ := AND
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_atmost_m]
      have hwt0 := sat range_0
      have hwt1 := sat range_1
      simp [PredicateB_of_SymmetricB, S_atmost_m] at hwt0 hwt1
      cases hwt0
      case inl hwt0 =>
        left
        calc
          ↑(wt (fun i ↦ AND (xs i))) ≤ ↑(wt (xs · range_0)) := wt_AND xs
          _ ≤ b := by
            have := sat range_0
            simp [PredicateB_of_SymmetricB] at this
            assumption
      case inr hwt0 =>
        have : ∀ j, xs j range_0 = b1 := by
          apply wt_m.mp
          simp [PredicateB_of_SymmetricB]
          apply Subtype.coe_eq_of_eq_mk
          assumption
        convert hwt1 with j j <;> (
        simp [AND]
        split
        case isTrue h => exact Eq.symm h.2
        case isFalse h =>
          simp [this j] at h
          symm
          exact b0_of_not_b1 h
        )
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_AND
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_AND

lemma S_atleast_0_nontrivial {m b : ℕ} (hlb : 1 < b) (hub : b ≤ m) Φ :
  ∃ n, ¬ trivial_forB (P_of_S (S_atleast_0 hlb hub)) Φ n := by
  unfold trivial_forB
  push_neg
  use 2, {
    fs _ := OR
    app xs sat := by
      simp [PredicateB_of_SymmetricB, S_atleast_0]
      have hwt0 := sat range_0
      have hwt1 := sat range_1
      simp [PredicateB_of_SymmetricB, S_atleast_0] at hwt0 hwt1
      cases hwt0
      case inl hwt0 =>
        left
        calc
          ↑(wt (fun i ↦ OR (xs i))) ≥ ↑(wt (xs · range_0)) := wt_OR xs
          _ ≥ b := by
            have := sat range_0
            simp [PredicateB_of_SymmetricB] at this
            assumption
      case inr hwt0 =>
        have : ∀ j, xs j range_0 = b0 := by
          apply wt_0.mp
          simp [PredicateB_of_SymmetricB]
          apply Subtype.coe_eq_of_eq_mk
          assumption
        convert hwt1 with j j <;> (
        simp [OR]
        split
        case isTrue h => exact Eq.symm h.2
        case isFalse h =>
          simp [this j] at h
          symm
          exact b1_of_not_b0 h
        )
  }
  constructor
  · apply not_dictator_of_dep
    use range_0
    apply dep_OR
  · apply not_certificate_of_nonconst
    intro i
    apply nonconst_OR

lemma S_comp_closed_nontrivial {S} (hS : is_comp_closed S) :
  ¬ trivial_for₁B (P_of_S S) (Φ_id (P_of_S S)) := by
  unfold trivial_for₁B
  push_neg
  use {
    fs _ := NEG
    app x Px := by
      simp [PredicateB_of_SymmetricB] at Px
      simp [PredicateB_of_SymmetricB]
      convert (hS _).mp Px
      apply wt_NEG_vec
  }
  constructor
  · unfold is_dictatorship₁B
    simp [Φ_id]
    by_contra! h
    replace h := congrFun h range_0
    replace h := congrFun h b0
    simp [NEG, ID, b0, b1] at h
  · by_contra! h
    obtain ⟨c, hc⟩ := h
    obtain ⟨i, hi⟩ := dom_nonemptyB c
    have h0 := congrFun (hc ⟨i, hi⟩) b0
    have h1 := congrFun (hc ⟨i, hi⟩) b1
    simp [NEG, b0, b1] at h0 h1
    rw [←h0] at h1
    contradiction
