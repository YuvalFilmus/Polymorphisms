-- in this file we define symmetric Boolean predicatesm

import Polymorphisms.Boolean
import Polymorphisms.BooleanAux
open Finset

def range_l {m} [i : AtLeast1 m] : range m :=
  ⟨m-1, by apply mem_range.mpr; have := i.1; omega⟩

@[ext]
structure SymmetricB where
  -- width
  m : ℕ
  -- weights
  W : Finset (range (m+1))
  -- nontriviality
  notall0 : ∃ w ∈ W, w.1 > 0
  notall1 : ∃ w ∈ W, w.1 < m
  notfull : ∃ w, w ∉ W

lemma symmetric_m_ge_2 (S : SymmetricB) : S.m ≥ 2 := by
  cases hm : S.m
  case zero =>
    obtain ⟨w, _, hw⟩ := S.notall0
    have := mem_range.mp w.coe_prop
    omega
  case succ m' =>
  cases hm' : m'
  case zero =>
    obtain ⟨w₁, w₁_in, hw₁⟩ := S.notall0
    obtain ⟨w₀, w₀_in, hw₀⟩ := S.notall1
    replace hw₀ : w₀.1 = 0 := by omega
    have := mem_range.mp w₁.coe_prop
    replace hw₁ : w₁.1 = 1 := by omega
    obtain ⟨w, w_notin⟩ := S.notfull
    exfalso
    contrapose! w_notin
    cases hw : w.1
    case zero =>
      have : w = w₀ := by aesop
      aesop
    case succ w' =>
    cases hw' : w'
    case zero =>
      have : w = w₁ := by aesop
      aesop
    case succ w'' =>
      have := mem_range.mp w.coe_prop
      omega
  case succ m'' =>
    omega

instance {S : SymmetricB} : AtLeast2 S.m :=
  ⟨symmetric_m_ge_2 S⟩

--@[simp]
def coe_vec {m} (x : range m → range 2) : ℕ → ℕ :=
  fun i => if h : i < m then (x ⟨i, mem_range.mpr h⟩).1 else 0

@[simp]
def wt' m (x : ℕ → ℕ) :=
  ∑ i ∈ range m, x i

@[simp]
def wt_val {m} (x : range m → range 2) :=
  wt' m (coe_vec x)

lemma wt_prop {m} (x : range m → range 2) : wt_val x ∈ range (m+1) := by
  apply mem_range.mpr
  let x' := coe_vec x
  calc
    ∑ i ∈ range m, x' i ≤ ∑ i ∈ range m, 1 := by
      apply sum_le_sum
      intro i hi
      simp [x', coe_vec, mem_range.mp hi]
      have := mem_range.mp (x ⟨i, hi⟩).coe_prop
      omega
    _ = m := by aesop
    _ < m+1 := by omega

def wt {m} (x : range m → range 2) : range (m+1) :=
  ⟨wt_val x, wt_prop x⟩

def permute {m} (e : Equiv.Perm (range m)) (x : range m → range 2)
  (i : range m) : range 2 := x (e i)

@[simp]
def permute_inv {m} (e : Equiv.Perm (range m)) (x : range m → range 2) :
  permute e⁻¹ (permute e x) = x := by
  funext i
  simp [permute]

@[simp]
def permute_inv' {m} (e : Equiv.Perm (range m)) (x : range m → range 2) :
  permute e (permute e⁻¹ x) = x := by
  funext i
  simp [permute]

@[simp]
lemma wt_of_wt {m} (x : range m → range 2) (e : Equiv.Perm (range m)) :
  wt (permute e x) = wt x := by
  symm
  simp [wt]
  unfold permute
  let e' : ℕ ↪ ℕ :=
  {
    toFun n := if h : n ∈ range m then e ⟨n, h⟩ else n
    inj' := by
      intro i j
      simp
      by_cases i < m
      case pos hi =>
        simp [hi]
        by_cases j < m
        case pos hj =>
          simp [hj]
          intro h
          have := e.left_inv.injective (Subtype.coe_eq_of_eq_mk h)
          simp [Subtype.mk.injEq] at this
          assumption
        case neg hj =>
          simp [hj]
          intro h
          exfalso
          apply hj
          rw [←h]
          apply mem_range.mp
          apply coe_mem (e ⟨i, _⟩)
      case neg hi =>
        simp [hi]
        by_cases j < m
        case neg hj =>
          simp [hj]
        case pos hj =>
          simp [hj]
          intro h
          exfalso
          apply hi
          rw [h]
          apply mem_range.mp
          apply coe_mem (e ⟨j, _⟩)
  }
  have he' : map e' (range m) = range m := by
    apply map_eq_of_subset
    intro i hi
    simp [map] at hi
    obtain ⟨a, ha, he'a⟩ := hi
    subst he'a
    simp [e', ha]
  have := sum_map (range m) e' (coe_vec x ·)
  rw [he'] at this
  rw [this]
  congr
  funext i
  simp [e', coe_vec]
  split
  case isTrue h =>
    split
    rfl
    case isFalse h' =>
      exfalso
      apply h'
      apply mem_range.mp
      apply coe_mem (e ⟨i, _⟩)
  case isFalse h =>
    rfl

def std_vec {m} (w : range (m+1)) : range m → range 2 :=
  fun i => if i.1 < w then b1 else b0

@[simp]
lemma wt_std_vec {m} {w : range (m+1)} : wt (std_vec w) = w := by
  apply Subtype.coe_eq_of_eq_mk
  let s := coe_vec (@std_vec m w)
  simp [wt]
  have := calc
    ∑ i ∈ range m, s i = ∑ i ∈ range ↑w ∪ Ico ↑w m, s i := by
      congr
      rw (occs := .pos [1, 2]) [range_eq_Ico]
      symm
      apply Ico_union_Ico_eq_Ico
      simp
      have := mem_range.mp w.coe_prop; omega
    _ = (∑ i ∈ range ↑w, s i) + ∑ i ∈ Ico ↑w m, s i := by
      rw (occs := .pos [1, 4]) [range_eq_Ico]
      apply sum_union
      apply Ico_disjoint_Ico_consecutive
    _ = (∑ i ∈ range ↑w, 1) + ∑ i ∈ Ico ↑w m, s i := by
      congr 1
      apply sum_congr rfl
      intro i hi
      have : i < m := by
        have := mem_range.mp hi
        have := mem_range.mp w.coe_prop
        omega
      simp [s, coe_vec, std_vec, this, mem_range.mp hi, b1]
    _ = (∑ i ∈ range ↑w, 1) + ∑ i ∈ Ico ↑w m, 0 := by
      congr 1
      apply sum_congr rfl
      intro i hi
      have : ¬ (i < w) := by
        have := mem_Ico.mp hi
        omega
      simp [s, coe_vec, std_vec, this, mem_Ico.mp hi, b0]
    _ = w := by
      aesop
  simp [s] at this
  assumption

def transposition {m} (i j : range m) : Equiv.Perm (range m) :=
{
  toFun k := if k = i then j else if k = j then i else k
  invFun k := if k = i then j else if k = j then i else k
  left_inv := by
    intro k
    by_cases k = i
    case pos hi => simp [hi]
    case neg hi =>
    simp [hi]
    by_cases k = j
    case pos hj => simp [hj]
    case neg hj => simp [hj]
  right_inv := by
    intro k
    by_cases k = i
    case pos hi => simp [hi]
    case neg hi =>
    simp [hi]
    by_cases k = j
    case pos hj => simp [hj]
    case neg hj => simp [hj]
}

lemma le_val {m} {a b : range m} (h : a ≤ b) : a.1 ≤ b.1 := h

def PredicateB_of_SymmetricB (S : SymmetricB) : PredicateB :=
{
  m := S.m,
  hm := by have := symmetric_m_ge_2 S; omega,
  P y := wt y ∈ S.W,
  full i σ := by
    obtain ⟨w₀, w₀_in_W, hw₀⟩ := S.notall1
    obtain ⟨w₁, w₁_in_W, hw₁⟩ := S.notall0
    let w := if σ = b0 then w₀ else w₁
    have w_in_W : w ∈ S.W := by
      cases h: of_range_2B σ
      case inl hw => simpa [w, hw]
      case inr hw => simpa [w, hw]
    let z := std_vec w
    let k : range S.m := if σ = b0 then range_l else range_0
    have hk : z k = σ := by
      cases of_range_2B σ
      case inl h0 =>
        simp [z, std_vec, h0, w, k, range_l]
        intro h
        omega
      case inr h1 =>
        simp [z, std_vec, h1, w, k, b0, b1, range_0]
        intro h
        omega
    let x := permute (transposition i k) z
    use x
    constructor
    · simp [x]
      rw [wt_std_vec]
      assumption
    · simpa [x, permute, transposition]
  dep i := by
    have Wne : S.W.Nonempty := by
      obtain ⟨w, hw, _⟩ := S.notall0
      use w, hw
    let minW := min' S.W Wne
    let minW_val : ℕ := minW
    have minW_prop := min'_mem S.W Wne
    cases hminW_val : minW_val
    case succ w =>
      let w' : range (S.m+1) := ⟨w, by
        apply mem_range.mpr
        have := mem_range.mp (coe_mem minW)
        simp [minW_val] at hminW_val
        omega
      ⟩
      let w'' : range S.m := ⟨w, by
        apply mem_range.mpr
        have := mem_range.mp (coe_mem minW)
        simp [minW_val] at hminW_val
        omega
      ⟩
      have hw' : w' ∉ S.W := by
        by_contra! hw'
        have := le_val (min'_le S.W w' hw')
        have := calc
          w + 1 = minW_val := Eq.symm hminW_val
          _ = (S.W.min' Wne).1 := by aesop
          _ ≤ w := by aesop
        omega
      let minW' : range S.m := ⟨minW, by
        apply mem_range.mpr
        obtain ⟨t, ht_in, ht_val⟩ := S.notall1
        have := le_val (min'_le S.W t ht_in)
        simp [minW]
        omega
      ⟩
      let x := std_vec minW
      let y := std_vec w'
      have hdiff (i : range S.m) (hi : i ≠ w'') : x i = y i := by
        simp [x, y, std_vec]
        split
        case isTrue h =>
          split
          case isTrue => rfl
          case isFalse h' =>
          push_neg at h'
          have : i.1 < minW_val := by aesop
          have : i.1 < w + 1 := by rwa [←hminW_val]
          have : w ≤ i.1 := by aesop
          have : i.1 = w := by omega
          exfalso; apply hi
          aesop
        case isFalse h =>
          split
          case isFalse => rfl
          case isTrue h' =>
          push_neg at h
          have : i.1 < w := by aesop
          have : minW_val ≤ i.1 := by aesop
          have : w + 1 ≤ i.1 := by rwa [←hminW_val]
          omega
      let e := transposition w'' i
      use permute e x, permute e y
      constructor
      simpa [x]
      constructor
      simpa [y]
      intro i' hi'
      simp [permute, e, transposition]
      split
      case isTrue h =>
        apply hdiff
        rw [←h]
        symm; assumption
      case isFalse h =>
        push_neg at h
        apply hdiff
        assumption
    case zero =>
      let Wc : Finset (range (S.m+1)) := {w | w ∉ S.W}
      have Wcne : Wc.Nonempty := by
        obtain ⟨w, hw⟩ := S.notfull
        use w
        simp [Wc]
        exact hw
      let minWc := min' Wc Wcne
      let minWc_val : ℕ := minWc
      have minWc_prop := min'_mem Wc Wcne
      cases hminWc_val : minWc_val
      case zero =>
        have hW : range_0 ∈ S.W := by
          convert minW_prop
          simp [range_0]
          conv =>
            left; arg 1; rw [←hminW_val]
        have hWc : range_0 ∈ Wc := by
          convert minWc_prop
          simp [range_0]
          conv =>
            left; arg 1; rw [←hminWc_val]
        simp [Wc] at hWc
        contradiction
      case succ w =>
      let w' : range (S.m+1) := ⟨w, by
        apply mem_range.mpr
        have := mem_range.mp (coe_mem minWc)
        simp [minWc_val] at hminWc_val
        omega
      ⟩
      let w'' : range S.m := ⟨w, by
        apply mem_range.mpr
        have := mem_range.mp (coe_mem minWc)
        simp [minWc_val] at hminWc_val
        omega
      ⟩
      have hw' : w' ∈ S.W := by
        by_contra! hw'
        have := le_val (min'_le Wc w' (by simp [Wc]; exact hw'))
        have := calc
          w + 1 = minWc_val := Eq.symm hminWc_val
          _ = (Wc.min' Wcne).1 := by aesop
          _ ≤ w := by aesop
        omega
      let minW' : range S.m := ⟨minW, by
        apply mem_range.mpr
        obtain ⟨t, ht_in, ht_val⟩ := S.notall1
        have := le_val (min'_le S.W t ht_in)
        simp [minW]
        omega
      ⟩
      let x := std_vec minWc
      let y := std_vec w'
      have hdiff (i : range S.m) (hi : i ≠ w'') : y i = x i := by
        symm
        simp [x, y, std_vec]
        split
        case isTrue h =>
          split
          case isTrue => rfl
          case isFalse h' =>
          push_neg at h'
          have : i.1 < minWc_val := by aesop
          have : i.1 < w + 1 := by rwa [←hminWc_val]
          have : w ≤ i.1 := by aesop
          have : i.1 = w := by omega
          exfalso; apply hi
          aesop
        case isFalse h =>
          split
          case isFalse => rfl
          case isTrue h' =>
          push_neg at h
          have : i.1 < w := by aesop
          have : minWc_val ≤ i.1 := by aesop
          have : w + 1 ≤ i.1 := by rwa [←hminWc_val]
          omega
      let e := transposition w'' i
      use permute e y, permute e x
      constructor
      simpa [y]
      constructor
      simp [Wc] at minWc_prop
      simpa [x]
      intro i' hi'
      simp [permute, e, transposition]
      split
      case isTrue h =>
        apply hdiff
        rw [←h]
        symm; assumption
      case isFalse h =>
        push_neg at h
        apply hdiff
        assumption
}

instance {S : SymmetricB} : AtLeast2 (PredicateB_of_SymmetricB S).m :=
  ⟨symmetric_m_ge_2 S⟩

lemma mem_symmetric_of_mem_predicate {S : SymmetricB}
  {x} (h : (PredicateB_of_SymmetricB S).P x) : wt x ∈ S.W := by
  simp [PredicateB_of_SymmetricB] at h
  exact h

lemma mem_std_vec {S : SymmetricB} {w : range (S.m+1)} :
  (PredicateB_of_SymmetricB S).P (std_vec w) ↔ w ∈ S.W := by
  simp [PredicateB_of_SymmetricB]

lemma predicate_symmetric (S : SymmetricB) (x : range S.m → range 2) (e : Equiv.Perm (range S.m))
  (Px : (PredicateB_of_SymmetricB S).P x) : (PredicateB_of_SymmetricB S).P (permute e x) := by
  simp [PredicateB_of_SymmetricB]
  simp [PredicateB_of_SymmetricB] at Px
  assumption

lemma predicate_symmetric_iff (S : SymmetricB) (x : range S.m → range 2) (e : Equiv.Perm (range S.m)) :
  (PredicateB_of_SymmetricB S).P x ↔ (PredicateB_of_SymmetricB S).P (permute e x) := by
  constructor
  · intro Px
    apply predicate_symmetric
    exact Px
  · intro Pex
    rw [←permute_inv e x]
    apply predicate_symmetric
    exact Pex

def permute_poly {S : SymmetricB} (e : Equiv.Perm (range S.m)) {n}
  (poly : PolymorphismB (PredicateB_of_SymmetricB S) n) : PolymorphismB (PredicateB_of_SymmetricB S) n :=
{
  fs i x := poly.fs (e i) x
  app xs sat := by
    simp
    suffices h : (PredicateB_of_SymmetricB S).P fun i ↦ poly.fs i (xs (e⁻¹ i)) by
      have := predicate_symmetric S _ e h
      unfold permute at this
      simp at this
      convert this with i
      symm
      apply Equiv.Perm.inv_apply_self
    have sat' i := predicate_symmetric S (xs · i) e⁻¹ (sat i)
    unfold permute at sat'
    apply poly.app _ sat'
}

def permute_poly₁ {S : SymmetricB} (e : Equiv.Perm (range S.m))
  (poly : Polymorphism₁B (PredicateB_of_SymmetricB S)) : Polymorphism₁B (PredicateB_of_SymmetricB S) :=
{
  fs i x := poly.fs (e i) x
  app y Py := by
    simp
    suffices h : (PredicateB_of_SymmetricB S).P fun i ↦ poly.fs i (y (e⁻¹ i)) by
      have := predicate_symmetric S _ e h
      unfold permute at this
      simp at this
      convert this with i
      symm
      apply Equiv.Perm.inv_apply_self
    have := predicate_symmetric S y e⁻¹ Py
    unfold permute at this
    apply poly.app _ this
}

@[simp]
def comp_val {m} (w : range (m+1)) : ℕ := m - w

lemma comp_prop {m} (w : range (m+1)) : comp_val w ∈ range (m+1) := by
  apply mem_range.mpr
  unfold comp_val
  omega

def comp {m} (w : range (m+1)) : range (m+1) :=
  ⟨comp_val w, comp_prop w⟩

@[simp]
lemma comp_comp {m} (w : range (m+1)) :
  comp (comp w) = w := by
  simp [comp, comp_val]
  apply Subtype.coe_eq_of_eq_mk
  simp
  have := mem_range.mp w.coe_prop
  omega

def is_comp_closed (S : SymmetricB) :=
  ∀ w, w ∈ S.W ↔ comp w ∈ S.W

lemma comp_closed {S : SymmetricB}
  (h : ∀ w, w ∈ S.W → comp w ∈ S.W) : is_comp_closed S := by
  intro w
  constructor
  · intro hw
    exact h w hw
  · intro hcompw
    convert h (comp w) hcompw
    simp

def NEG_vec {m} (x : range m → range 2) (i : range m) : range 2 :=
  NEG (x i)

@[simp]
lemma NEG_NEG_vec {m} (x : range m → range 2) : NEG_vec (NEG_vec x) = x := by
  funext i
  simp [NEG_vec]

@[simp]
lemma wt_NEG_vec {m} (x : range m → range 2) :
  wt (NEG_vec x) = comp (wt x) := by
  simp [comp]
  apply Subtype.coe_eq_of_eq_mk
  have : wt x + wt (fun i ↦ NEG (x i)) = m := calc
    wt x + wt (fun i ↦ NEG (x i)) =
    ∑ i ∈ range m, coe_vec x i + ∑ i ∈ range m, coe_vec (fun i ↦ NEG (x i)) i := by
      simp [wt, PredicateB_of_SymmetricB]
    _ = ∑ i ∈ range m, (coe_vec x i + coe_vec (fun i ↦ NEG (x i)) i) := by
      rw [sum_add_distrib]
    _ = ∑ i ∈ range m, 1 := by
      apply sum_congr rfl
      intro i hi
      simp [coe_vec, hi, PredicateB_of_SymmetricB, mem_range.mp hi, NEG]
      split
      case isTrue h =>
        rw [h]
        simp [b0, b1]
      case isFalse h =>
        rw [b1_of_not_b0 h]
        simp [b0, b1]
    _ = m := by
      rw [sum_const, card_range]
      simp
  exact Nat.eq_sub_of_add_eq' this

-- the various standard symmetric sets

def S_even {m : ℕ} (hm : m ≥ 2) : SymmetricB :=
{
  m := m
  W := {w | Even w.1}
  notall0 := by
    use ⟨2, ?_⟩
    constructor <;> simp
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨0, ?_⟩
    constructor <;> simp
    omega
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨1, ?_⟩
    simp
    apply mem_range.mpr
    omega
}

def S_odd {m : ℕ} (hm : m ≥ 2) : SymmetricB :=
{
  m := m
  W := {w | Odd w.1}
  notall0 := by
    use ⟨1, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨1, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨0, ?_⟩
    simp
    apply mem_range.mpr
    omega
}

def S_atmost {m b : ℕ} (hlb : 0 < b) (hub : b < m) : SymmetricB :=
{
  m := m
  W := {w | w ≤ b}
  notall0 := by
    use ⟨1, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨0, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨b + 1, ?_⟩
    simp
    apply mem_range.mpr
    omega
}

def S_atleast {m b : ℕ} (hlb : 0 < b) (hub : b < m) : SymmetricB :=
{
  m := m
  W := {w | b ≤ w}
  notall0 := by
    use ⟨b, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨b, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨0, ?_⟩
    simp
    push_neg
    omega
    apply mem_range.mpr
    omega
}

def S_atmost_m {m b : ℕ} (hub : b+1 < m) : SymmetricB :=
{
  m := m
  W := {w | w ≤ b ∨ w = m}
  notall0 := by
    use ⟨m, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨0, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨b + 1, ?_⟩
    simp
    push_neg
    omega
    apply mem_range.mpr
    omega
}

def S_atleast_0 {m b : ℕ} (hlb : 1 < b) (hub : b ≤ m) : SymmetricB :=
{
  m := m
  W := {w | b ≤ w ∨ w = (0:ℕ)}
  notall0 := by
    use ⟨b, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notall1 := by
    use ⟨0, ?_⟩
    constructor <;> (simp; try omega)
    apply mem_range.mpr
    omega
  notfull := by
    use ⟨1, ?_⟩
    simp
    omega
    apply mem_range.mpr
    omega
}

def is_nontrivial_S (S : SymmetricB) :=
  (∃ (m : ℕ) (hm : m ≥ 2), S = S_even hm) ∨
  (∃ (m : ℕ) (hm : m ≥ 2), S = S_odd hm) ∨
  (∃ (m b : ℕ) (hlb : 0 < b) (hub : b < m), S = S_atmost hlb hub) ∨
  (∃ (m b : ℕ) (hlb : 0 < b) (hub : b < m), S = S_atleast hlb hub) ∨
  (∃ (m b : ℕ) (hub : b+1 < m), S = S_atmost_m hub) ∨
  (∃ (m b : ℕ) (hlb : 1 < b) (hub : b ≤ m), S = S_atleast_0 hlb hub)

-- the two Φ's

def Φ_id (pred : PredicateB) : Set (formatB pred) := { fun _ => ID }
def Φ_neg (pred : PredicateB) : Set (formatB pred) :=
  { φ | ∀ i, φ i = ID ∨ φ i = NEG }

lemma Φ_id_perm (pred : PredicateB) : permutationalB (Φ_id pred) := by
  intro φ hφ i
  simp [Φ_id] at hφ
  rw [hφ]
  apply bijective_ID

lemma Φ_neg_perm (pred : PredicateB) : permutationalB (Φ_neg pred) := by
  intro φ hφ i
  simp [Φ_neg] at hφ
  cases hφ i.1 (mem_range.mp i.property)
  case inl h => rw [h]; apply bijective_ID
  case inr h => rw [h]; apply bijective_NEG

abbrev P_of_S := PredicateB_of_SymmetricB

inductive Φ_type
| id
| neg

def Φ_std (t : Φ_type) (S : SymmetricB) : Set (formatB (P_of_S S)) :=
match t with
| .id => Φ_id (P_of_S S)
| .neg => Φ_neg (P_of_S S)

lemma Φ_std_perm (t : Φ_type) (S : SymmetricB) : permutationalB (Φ_std t S) := by
  cases t
  case id =>
    simp [Φ_std]
    apply Φ_id_perm
  case neg =>
   simp [Φ_std]
   apply Φ_neg_perm

lemma Φ_std_contains_ID (t : Φ_type) (S : SymmetricB) :
  (fun _ ↦ ID) ∈ Φ_std t S := by
  cases t
  case id =>
    simp [Φ_std, Φ_id]
  case neg =>
    simp only [Φ_std, Φ_neg]
    apply Set.mem_setOf.mpr
    simp

-- auxiliary results

lemma wt_0 {m} {x : range m → range 2} :
  wt x = ⟨0, by aesop⟩ ↔ ∀ i, x i = b0 := by
  constructor
  · intro h
    contrapose! h
    obtain ⟨i₀, hi₀⟩ := h
    replace hi₀ := b1_of_not_b0 hi₀
    suffices (wt x : ℕ) ≥ 1 by
      by_contra! h
      simp [h] at this
    calc
      wt x = ∑ i ∈ range m, coe_vec x i := by simp [wt]
      _ = coe_vec x i₀ + ∑ i ∈ (range m).erase i₀, coe_vec x i := by
        rw [add_sum_erase]
        exact i₀.property
      _ = 1 + ∑ i ∈ (range m).erase i₀, coe_vec x i := by
        simp [coe_vec, mem_range.mp i₀.property, hi₀, b1]
      _ ≥ 1 := by
        omega
  · intro h
    apply Subtype.coe_eq_of_eq_mk
    calc
      wt x = ∑ i ∈ range m, coe_vec x i := by simp [wt]
      _ = ∑ i ∈ range m, 0 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp hi]
        rw [h ⟨i, hi⟩]
        simp [b0]
      _ = 0 := by
        apply sum_const

lemma wt_m {m} {x : range m → range 2} :
  wt x = ⟨m, by aesop⟩ ↔ ∀ i, x i = b1 := by
  constructor
  · intro h
    by_cases m = 0
    case pos hm =>
      intro i
      have := mem_range.mp i.property
      omega
    case neg hm =>
    have : m ≥ 1 := by omega
    contrapose! h
    obtain ⟨i₀, hi₀⟩ := h
    replace hi₀ := b0_of_not_b1 hi₀
    suffices (wt x : ℕ) ≤ m - 1 by
      by_contra! h
      simp [h] at this
      have : m+1 ≤ m := by omega
      omega
    calc
      wt x = ∑ i ∈ range m, coe_vec x i := by simp [wt]
      _ = coe_vec x i₀ + ∑ i ∈ (range m).erase i₀, coe_vec x i := by
        rw [add_sum_erase]
        exact i₀.property
      _ = ∑ i ∈ (range m).erase i₀, coe_vec x i := by
        simp [coe_vec, mem_range.mp i₀.property, hi₀, b0]
      _ ≤ ∑ i ∈ (range m).erase i₀, 1 := by
        apply sum_le_sum
        intro i hi
        have hi' : i ∈ range m := (mem_erase.mp hi).2
        simp [coe_vec, mem_range.mp hi']
        have := mem_range.mp (x ⟨i, hi'⟩).property
        omega
      _ ≤ m - 1 := by
        rw [sum_const, card_erase_of_mem, card_range]
        simp
        exact i₀.property
  · intro h
    apply Subtype.coe_eq_of_eq_mk
    calc
      wt x = ∑ i ∈ range m, coe_vec x i := by simp [wt]
      _ = ∑ i ∈ range m, 1 := by
        apply sum_congr rfl
        intro i hi
        simp [coe_vec, mem_range.mp hi]
        rw [h ⟨i, hi⟩]
        simp [b1]
      _ = m := by
        rw [sum_const, card_range]
        simp
