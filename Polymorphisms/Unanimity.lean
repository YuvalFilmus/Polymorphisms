-- in this file we draw a connection to Dokow-Holzman impossibility domains

import Polymorphisms.Basic
import Polymorphisms.ReductionTo2
import Polymorphisms.ReductionTo1
import Polymorphisms.Bijection
open Finset

variable {pred : Predicate}

def const {t₁ t₂ : Type} (σ : t₂) (_ : t₁) := σ

def unanimous {n} (poly : Polymorphism pred n) :=
  ∀ i : range pred.m, ∀ σ : range (pred.a i), poly.fs i (const σ) = σ

def impossibility_domain (pred : Predicate) :=
  ∀ ⦃n⦄, n ≥ 1 → ∀ ⦃poly : Polymorphism pred n⦄, unanimous poly →
    ∃ j, ∀ i x, poly.fs i x = x j

def pop {t : Type} {n : ℕ} (x : range (n+1) → t) (i : range n) : t :=
  x ⟨i+1, by
    apply mem_range.mpr
    have := mem_range.mp i.coe_prop
    linarith
  ⟩

def iterate_poly_2 {pred : Predicate} (poly : Polymorphism pred 2)
  (r : ℕ) : Polymorphism pred (r+1) :=
  match r with
  | 0 =>
  {
    fs i x := x range_0,
    app xs sat := sat range_0
  }
  | r'+1 =>
  {
    fs i x := poly.fs i (cons_input (x range_0) ((iterate_poly_2 poly r').fs i (pop x))),
    app xs sat := by
      apply poly.app
      intro j
      cases of_range_2 j
      case inl hj =>
        simp [hj, cons_input]
        apply sat
      case inr hj =>
        simp [hj, cons_input, range_0, range_1]
        apply (iterate_poly_2 poly r').app
        intro j
        let j' : range (r'+1+1) := ⟨j+1, by
          apply mem_range.mpr
          have := mem_range.mp j.coe_prop
          linarith
        ⟩
        convert (sat j') with i
  }

@[simp]
lemma pop_const {t : Type} {n : ℕ} (σ : t) :
  pop (const σ : range (n+1) → t) = const σ := by
  funext i
  simp [pop, const]

def π_func {pred} (poly : Polymorphism pred 2)
  (i : range pred.m) (σ τ : range (pred.a i)) :=
  poly.fs i (cons_input σ τ)

def const_last {t : Type} {r : ℕ} (σ τ : t) (j : range r) :=
  if ↑j+1 = r then τ else σ

@[simp]
lemma pop_const_last {t : Type} {n : ℕ} (σ τ : t) :
  pop (const_last σ τ : range (n+1) → t) = const_last σ τ := by
  funext i
  simp [pop, const_last]

@[simp]
lemma const_of_const_last {t : Type} {r : ℕ} {σ : t} :
  (const_last σ σ : range r → t) = const σ := by
  unfold const_last
  unfold const
  funext j
  simp

lemma iterate_const_last {pred : Predicate} (poly : Polymorphism pred 2)
  (r : ℕ) (i : range pred.m) (σ τ : range (pred.a i)) :
  (iterate_poly_2 poly r).fs i (const_last σ τ) =
  (π_func poly i σ)^[r] τ := by
  induction r
  case zero =>
    simp [iterate_poly_2, const_last, range_0]
  case succ r' ih =>
    simp only [iterate_poly_2]
    rw [pop_const_last, ih, const_last]
    symm
    apply Function.iterate_succ_apply'

lemma iterate_const {pred : Predicate} (poly : Polymorphism pred 2)
  (r : ℕ) (i : range pred.m) (σ : range (pred.a i)) :
  (iterate_poly_2 poly r).fs i (const σ) =
  (π_func poly i σ)^[r] σ := by
  rw [←const_of_const_last, iterate_const_last poly r i σ σ]

def max_a (pred : Predicate) : ℕ :=
  max' (image pred.a univ) (by use pred.a range_0; simp)

def r_pred (pred : Predicate) :=
  (max_a pred).factorial

lemma iterate_poly_2_unanimous {pred : Predicate} {poly : Polymorphism pred 2}
  (hLatin : ∀ i, is_Latin_square (poly.fs i)) :
  unanimous (iterate_poly_2 poly (r_pred pred)) := by
  intro i σ
  rw [iterate_const poly (r_pred pred) i σ]
  have hbijective : (π_func poly i σ).Bijective := by
    unfold π_func
    apply (hLatin i).1
  have hdvd : (pred.a i).factorial ∣ (r_pred pred) := by
    unfold r_pred
    apply Nat.factorial_dvd_factorial
    apply le_max'
    simp
  have := lagrange_bijective hbijective hdvd
  apply congrFun this

def const_0 {t : Type} {r : ℕ} (σ τ : t) (j : range r) :=
  if j.1 = 0 then σ else τ

@[simp]
lemma pop_const_0 {t : Type} {r : ℕ} (σ τ : t) :
  pop (const_0 σ τ : range (r+1) → t) = const τ := by
  funext j
  simp [pop, const, const_0]

lemma iterate_const_0 {pred : Predicate} (poly : Polymorphism pred 2)
  {r : ℕ} (i : range pred.m) (σ τ : range (pred.a i)) :
  (iterate_poly_2 poly (r+1)).fs i (const_0 σ τ) =
  π_func poly i σ ((π_func poly i τ)^[r] τ) := by
  match r with
  | 0 =>
    simp [iterate_poly_2, π_func, const_0, range_0]
    rfl
  | r'+1 =>
    rw [←iterate_const poly (r'+1) i τ]
    conv =>
      left
      unfold iterate_poly_2
    simp [π_func, const_0, range_0]

lemma iterate_poly_2_not_dictator {pred : Predicate} (poly : Polymorphism pred 2)
  {r : ℕ} (hr : r ≥ 1)
  (i : range pred.m) (hLatin : is_Latin_square (poly.fs i))
  (j : range (r+1)):
  ∃ x, (iterate_poly_2 poly r).fs i x ≠ x j := by
  have hr' : 0 ≠ r := by linarith
  by_cases j = range_0
  case pos hj =>
    subst hj
    by_contra! hdict'
    have hdict (σ : range (pred.a i)) := hdict' (const_last range_0 σ)
    conv at hdict =>
      ext σ
      rw [iterate_const_last poly r i range_0 σ]
      simp [const_last]
    conv at hdict =>
      ext σ
      right
      simp [range_0, hr']
    have h0 := hdict range_0
    have h1 := hdict range_1
    have hbijective : (π_func poly i range_0)^[r].Bijective := by
      apply Function.Bijective.iterate
      unfold π_func
      apply hLatin.1
    have := hbijective.1 (Eq.trans h0 (Eq.symm h1))
    simp [range_0, range_1] at this
  case neg hj =>
    by_contra! hdict'
    have hdict (σ : range (pred.a i)) := hdict' (const_0 σ range_0)
    have hj' : j.1 ≠ 0 := by
      contrapose! hj
      apply Subtype.eq
      simpa [range_0]
    conv at hdict =>
      ext σ
      simp [const_0, hj']
      unfold iterate_poly_2
    split at hdict
    case _ => contradiction
    case _ r' =>
    conv at hdict =>
      ext σ
      simp [const_0, range_0]
    have h0 := hdict range_0
    have h1 := hdict range_1
    have := (hLatin.2 _).1 (Eq.trans h0 (Eq.symm h1))
    simp [range_0, range_1] at this

theorem trivial_iff_impossibility {pred Φ}
  (hperm : permutational Φ)
  (htrivial : trivial_for₁ pred Φ) :
  (∀ n, trivial_for pred Φ n) ↔ impossibility_domain pred := by
  constructor
  case mp =>
    contrapose!
    intro h
    unfold impossibility_domain at h
    push_neg at h
    obtain ⟨n, hn, poly, hunanimous, hnondictator⟩ := h
    use n
    unfold trivial_for
    push_neg
    use poly
    constructor
    · by_contra! h
      obtain ⟨j, φ, _, hdict⟩ := h
      obtain ⟨i, x, hnondict⟩ := hnondictator j
      apply hnondict
      rw [hdict i x]
      have := hdict i (const (x j))
      simp [const] at this
      rw [hunanimous i (x j)] at this
      symm; assumption
    · unfold is_certificate
      push_neg
      intro c
      obtain ⟨i', hi'⟩ := dom_nonempty c
      let i : c.dom := ⟨i', hi'⟩
      use i
      let σ : range (pred.a i) := if c.ρ i = range_0 then range_1 else range_0
      use const σ
      rw [hunanimous i σ]
      simp [σ]
      split
      case isTrue h => rw [h]; simp [range_0, range_1]
      case isFalse h => contrapose! h; symm; exact h
  case mpr =>
    intro himpossibility
    apply (trivial_iff_trivial_for_2 pred Φ).mpr
    contrapose! himpossibility
    unfold impossibility_domain
    push_neg
    cases trivial_for_2_of_trivial_for_1 hperm htrivial
    case inl => contradiction
    case inr h =>
    cases h
    case inl hclosure =>
      obtain ⟨i₀, σ₀, hclosed⟩ := hclosure
      use 2
      constructor
      omega
      let e : Polymorphism pred 2 :=
      {
        fs i x :=
          if h : i = i₀ then
            let σ : range (pred.a i) :=
              ⟨σ₀, by
                apply mem_range.mpr
                convert mem_range.mp σ₀.2
              ⟩
            if x range_1 = σ then
              σ
            else
              x range_0
            else
              x range_0
        app xs sat := by
          by_cases xs i₀ range_1 = σ₀
          case pos h =>
            convert hclosed (xs · range_0) (sat range_0) with i
            simp [set_coord_to]
            split
            case isTrue h' =>
              subst h h'
              simp
            case isFalse h' =>
              rfl
          case neg h =>
            convert (sat range_0) with i
            simp
            intro h'
            subst h'
            simp [h]
      }
      use e
      constructor
      · intro i σ
        simp [e, const]
        intro h
        subst h
        intro h
        rw [h]
      · let σ₁ : range (pred.a i₀) := if σ₀ = range_0 then range_1 else range_0
        have hσ₀σ₁ : σ₀ ≠ σ₁ := by
          simp [σ₁]
          split
          case isTrue h => subst h; simp [range_0, range_1]
          case isFalse h => exact h
        intro j
        use i₀
        cases of_range_2 j
        case inl hj =>
          subst hj
          use cons_input σ₁ σ₀
          simpa [e, cons_input, range_0, range_1]
        case inr hj =>
          subst hj
          use cons_input σ₀ σ₁
          simpa [e, cons_input, range_0, range_1]
    case inr h =>
    cases h
    case inl hANDOR =>
      obtain ⟨⟨i, hi⟩, poly, hbool, hnonbool⟩ := hANDOR
      use 2
      constructor
      omega
      use poly
      constructor
      · intro i σ
        by_cases pred.a i = 2
        case pos ha =>
          cases hbool i ha
          case inl hAND =>
            simp [hAND, AND₂, const]
            cases of_range_2' ha σ
            case inl h => subst h; simp [range_0, range_1]
            case inr h => subst h; simp [range_0, range_1]
          case inr hOR =>
            simp [hOR, OR₂, const]
            cases of_range_2' ha σ
            case inl h => subst h; simp [range_0, range_1]
            case inr h => subst h; simp [range_0, range_1]
        case neg ha =>
          replace ha : pred.a i > 2 := by have := pred.ha i; omega
          rw [hnonbool i ha]
          simp [const]
      · intro j
        use i
        cases hbool i hi
        case inl hfs =>
          rw [hfs]
          cases of_range_2 j
          case inl hj =>
            use cons_input range_1 range_0
            simp [AND₂, hj, cons_input, range_0, range_1]
          case inr hj =>
            use cons_input range_0 range_1
            simp [AND₂, hj, cons_input, range_0, range_1]
        case inr hfs =>
          rw [hfs]
          cases of_range_2 j
          case inl hj =>
            use cons_input range_0 range_1
            simp [OR₂, hj, cons_input, range_0, range_1]
          case inr hj =>
            use cons_input range_1 range_0
            simp [OR₂, hj, cons_input, range_0, range_1]
    case inr hLatin =>
      obtain ⟨poly, hLatin⟩ := hLatin
      replace hLatin := is_Latin_square_of_is_Latin_square_poly hperm hLatin
      use (r_pred pred) + 1
      constructor
      linarith
      use iterate_poly_2 poly (r_pred pred)
      constructor
      apply iterate_poly_2_unanimous hLatin
      intro j
      use range_0
      apply iterate_poly_2_not_dictator
      · unfold r_pred
        apply Nat.factorial_pos
      apply hLatin
