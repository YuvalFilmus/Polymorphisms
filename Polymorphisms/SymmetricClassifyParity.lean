import Polymorphisms.SymmetricClassify
open Finset

namespace Nat.ModEq

-- is this really not in Mathlib?
lemma sum {α} [DecidableEq α] {s : Finset α} {f g : α → ℕ} {m} (h : ∀ x ∈ s, f x ≡ g x [MOD m]) :
  ∑ x ∈ s, f x ≡ ∑ x ∈ s, g x [MOD m] := by
  induction s using Finset.induction
  case empty =>
    simp
    rfl
  case insert a y ha hind =>
    rw [sum_insert ha, sum_insert ha]
    apply Nat.ModEq.add
    · apply h
      simp
    · apply hind
      intro x hx
      apply h
      apply mem_insert_of_mem
      exact hx

end Nat.ModEq

namespace NontrivialType

def XOR {n} (J : Finset (range n)) (b : range 2) (x : range n → range 2) : range 2 := by
  use (∑ j ∈ J, (x j).val + b.val) % 2
  apply mem_range.mpr
  omega

def wt_alt {m} (x : range m → range 2) :
  (wt x).val = ∑ j : range m, (x j).val := by
  simp [wt]
  let e : range m ↪ ℕ := {
    toFun i := i.val,
    inj' := by simp
  }
  convert sum_map (range m).attach e (coe_vec x ·) with _ _ i hi
  · ext i
    constructor
    · intro hi
      apply mem_map.mpr
      use ⟨i, hi⟩
      simp [e]
    · intro hi
      simp [e] at hi
      apply mem_range.mpr
      assumption
  · simp [coe_vec, e, mem_range.mp i.property]

lemma parity_polymorphisms_if {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  (n : ℕ) (J : Finset (range n)) (b : range P.m → range 2)
  (hb : ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2]) :
  ∃ poly : PolymorphismB P n, poly.fs = fun i ↦ XOR J (b i) := by
  obtain ⟨Pm, PP⟩ := parity_def h
  symm at Pm
  subst Pm
  use {
    fs i := XOR J (b i),
    app xs sat := by
      apply (PP _).mpr
      simp [wt_alt, XOR]
      calc
        ∑ i : range P.m, (∑ j ∈ J, ↑(xs i j) + ↑(b i)) % 2
        ≡ ∑ i : range P.m, (∑ j ∈ J, ↑(xs i j) + ↑(b i)) [MOD 2] := by
          simp [Nat.ModEq]
          rw [← @sum_nat_mod]
        _ ≡ ∑ i : range P.m, ∑ j ∈ J, ↑(xs i j) + ∑ i : range P.m, ↑(b i) [MOD 2] := by
          rw [sum_add_distrib]
        _ ≡ ∑ i : range P.m, ∑ j ∈ J, ↑(xs i j) + (#J + 1) * p [MOD 2] := by
          apply Nat.ModEq.add_left
          assumption
        _ ≡ ∑ j ∈ J, ∑ i : range P.m, ↑(xs i j) + (#J + 1) * p [MOD 2] := by
          rw [sum_comm]
        _ ≡ ∑ j ∈ J, ↑p + (#J + 1) * p [MOD 2] := by
          apply Nat.ModEq.add_right
          apply Nat.ModEq.sum
          intro i hi
          rw [← wt_alt]
          apply (PP _).mp
          apply sat i
        _ ≡ #J * p + (#J + 1) * p [MOD 2] := by
          congr
          apply sum_const
        _ ≡ 2 * #J * p + p [MOD 2] := by
          congr 1
          ring
        _ ≡ 0 + p [MOD 2] := by
          apply Nat.ModEq.add_right
          apply Nat.modEq_zero_iff_dvd.mpr
          rw [mul_assoc]
          apply Nat.dvd_mul_right
        _ ≡ p [MOD 2] := by
          congr
          apply zero_add
  }

def Parity {m} (x : range m → range 2) : range 2 := by
  use (∑ j : range m, ↑(x j)) % 2
  apply mem_range.mpr
  apply Nat.mod_lt
  simp

lemma parity_def' {P m p hm} (h : P = P_of_S (parity m p hm).denotation) :
  P.m = m ∧ ∀ x, P.P x ↔ Parity x = p := by
  obtain ⟨Pm, PP⟩ := parity_def h
  symm at Pm
  subst Pm
  simp
  convert PP with x
  rw [wt_alt]
  unfold Parity
  constructor
  · intro h
    unfold Nat.ModEq
    rw [←h]
    simp
  · intro h
    apply Subtype.coe_eq_of_eq_mk
    simp
    unfold Nat.ModEq at h
    convert h
    have := mem_range.mp p.property
    omega

def parity_poly (p : range 2) {n m} (fs : range m → (range n → range 2) → range 2) :=
  ∀ (xs : range m → range n → range 2),
    (∀ j, Parity (xs · j) = p) → Parity (fun i ↦ fs i (xs i)) = p

def flip {m} (x : range m → range 2) (i₀ : range m) (i : range m) : range 2 :=
  if i = i₀ then NEG (x i) else x i

lemma NEG_add1 {b : range 2} :
  NEG b = ⟨(b.val + 1) % 2, by apply mem_range.mpr; omega⟩ := by
  cases of_range_2B b
  case inl h =>
    subst h
    simp [NEG, b0, b1]
  case inr h =>
    subst h
    simp [NEG, b0, b1]

@[simp]
lemma Parity_flip {m} (x : range m → range 2) (i₀ : range m) :
  Parity (flip x i₀) = NEG (Parity x) := by
  rw [NEG_add1]
  apply Subtype.coe_eq_of_eq_mk
  calc
    Parity (flip x i₀) = (∑ i : range m, (flip x i₀ i).val) % 2 := by
      simp [Parity]
    _ = (∑ i ∈ (range m).attach.erase i₀, (flip x i₀ i).val + (flip x i₀ i₀).val) % 2 := by
      congr
      rw [sum_erase_add] <;> simp
    _ = (∑ i ∈ (range m).attach.erase i₀, ↑(x i) + (flip x i₀ i₀).val) % 2 := by
      congr 2
      apply sum_congr rfl
      intro i hi
      replace hi := (mem_erase.mp hi).left
      simp [flip, hi]
    _ = (∑ i ∈ (range m).attach.erase i₀, ↑(x i) + NEG (x i₀)) % 2 := by
      congr
      simp [flip]
    _ = (∑ i ∈ (range m).attach.erase i₀, ↑(x i) + x i₀ + 1) % 2 := by
      simp [NEG_add1]
      omega
    _ = (∑ i : range m, ↑(x i) + 1) % 2 := by
      rw [sum_erase_add] <;> simp
    _ = (Parity x + 1) % 2 := by
      simp [Parity]

@[simp]
lemma XOR_flip_notin {m : ℕ} (J : Finset (range m)) (b : range 2) (j₀) (h : j₀ ∉ J) (x) :
  XOR J b (flip x j₀) = XOR J b x := by
  simp [XOR]
  congr 2
  apply sum_congr rfl
  intro j hj
  have : j ≠ j₀ := by
    contrapose! h
    subst h
    assumption
  simp [flip, this]

@[simp]
lemma XOR_flip_in {m : ℕ} (J : Finset (range m)) (b : range 2) (j₀) (h : j₀ ∈ J) (x) :
  XOR J b (flip x j₀) = NEG (XOR J b x) := by
  rw [NEG_add1]
  apply Subtype.coe_eq_of_eq_mk
  calc
    XOR J b (flip x j₀) = (∑ j ∈ J, (flip x j₀ j).val + b) % 2 := by
      simp [XOR]
    _ = (∑ j ∈ J.erase j₀, (flip x j₀ j).val + (flip x j₀ j₀).val + b) % 2 := by
      rw [sum_erase_add]
      exact h
    _ = (∑ j ∈ J.erase j₀, (x j).val + NEG (x j₀) + b) % 2 := by
      congr 2
      simp [flip]
      apply sum_congr rfl
      intro j hj
      simp [mem_erase.mp hj]
    _ = (∑ j ∈ J.erase j₀, (x j).val + x j₀ + b + 1) % 2 := by
      simp [NEG_add1]
      omega
    _ = (∑ j ∈ J, (x j).val + b + 1) % 2 := by
      rw [sum_erase_add]
      exact h
    _ = (XOR J b x + 1) % 2 := by
      simp [XOR]

def flip2 {m} (x : range m → range 2) (i₀ i₁ : range m) :=
  flip (flip x i₀) i₁

@[simp]
lemma Parity_flip2 {m} (x : range m → range 2) (i₀ i₁ : range m) :
  Parity (flip2 x i₀ i₁) = Parity x := by
  unfold flip2
  simp

def other_ix {m} (hm : m ≥ 3) (i₀ i₁ : range m) : range m :=
  have : AtLeast3 m := ⟨hm⟩
  if i₀ ≠ range_0 ∧ i₁ ≠ range_0 then
    range_0
  else if i₀ ≠ range_1 ∧ i₁ ≠ range_1 then
    range_1
  else
    range_2

lemma other_ix_spec {m} (hm : m ≥ 3) (i₀ i₁ : range m) :
  other_ix hm i₀ i₁ ≠ i₀ ∧ other_ix hm i₀ i₁ ≠ i₁ := by
  simp [other_ix, range_0, range_1, range_2]
  split
  case isTrue h =>
    tauto
  case isFalse h =>
    split
    case isTrue h' =>
      tauto
    case isFalse h' =>
      constructor
      · by_contra! h''
        symm at h''
        subst h''
        simp at h
        simp at h'
        simp [h] at h'
      · by_contra! h''
        symm at h''
        subst h''
        simp at h
        simp at h'
        simp [h] at h'

def complete' {m} (hm : m ≥ 3) (i₀ i₁ : range m) (b₀ b₁ b₂ : range 2) (i : range m) : range 2 :=
  if i = i₀ then
    b₀
  else if i = i₁ then
    b₁
  else if i = other_ix hm i₀ i₁ then
    b₂
  else
    b0

@[simp]
lemma complete'_flip {m} (hm : m ≥ 3) (i₀ i₁ : range m) (b₀ b₁ b₂ : range 2) :
  flip (complete' hm i₀ i₁ b₀ b₁ b₂) (other_ix hm i₀ i₁) = complete' hm i₀ i₁ b₀ b₁ (NEG b₂) := by
  funext i
  simp [flip, complete']
  by_cases i = i₀
  case pos hi₀ =>
    subst hi₀
    by_cases i = i₁
    case pos hi₁ =>
      subst hi₁
      simp [(other_ix_spec hm i i).1.symm]
    case neg hi₁ =>
      simp [hi₁]
      simp [(other_ix_spec hm i i₁).1.symm]
  case neg hi₀ =>
    simp [hi₀]
    by_cases i = i₁
    case pos hi₁ =>
      subst hi₁
      simp [(other_ix_spec hm i₀ i).2.symm]
    case neg hi₁ =>
      simp [hi₁]
      split <;> rfl

def complete (p : range 2) {m} (hm : m ≥ 3) (i₀ i₁ : range m) (b₀ b₁ : range 2) : range m → range 2 :=
  if Parity (complete' hm i₀ i₁ b₀ b₁ b0) = p then
    complete' hm i₀ i₁ b₀ b₁ b0
  else
    complete' hm i₀ i₁ b₀ b₁ b1

lemma eq_of_eq_NEG {a b} (h : NEG a = NEG b) : a = b := by
  rw [← NEG_NEG a, ← NEG_NEG b]
  aesop

lemma complete_spec (p : range 2) {m} (hm : m ≥ 3) {i₀ i₁ : range m} (hi₀i₁ : i₀ ≠ i₁) (b₀ b₁ : range 2) :
  (complete p hm i₀ i₁ b₀ b₁ i₀ = b₀ ∧
   complete p hm i₀ i₁ b₀ b₁ i₁ = b₁) ∧
  Parity (complete p hm i₀ i₁ b₀ b₁) = p := by
  constructor
  · constructor
    all_goals unfold complete
    all_goals split
    all_goals unfold complete'
    all_goals simp [hi₀i₁.symm]
  · unfold complete
    split
    case isTrue h => exact h
    case isFalse h =>
      replace h := NEG_of_ne h
      have : b0 = NEG b1 := rfl
      rw [this, ← complete'_flip, Parity_flip] at h
      apply eq_of_eq_NEG h

def sensitive_f {n} (f : (range n → range 2) → range 2)
  (j : range n) := ∃ x, f (flip x j) = NEG (f x)

def sensitive {n m} (fs : range m → (range n → range 2) → range 2)
  (j : range n) := ∃ i, sensitive_f (fs i) j

noncomputable instance {n m} (fs : range m → (range n → range 2) → range 2) : DecidablePred (sensitive fs) := by
  unfold DecidablePred
  intro j
  unfold sensitive
  exact Classical.propDecidable (∃ i, sensitive_f (fs i) j)

def flippy_f {n} (f : (range n → range 2) → range 2)
  (j : range n) := ∀ x, f (flip x j) = NEG (f x)

def flippy {n m} (fs : range m → (range n → range 2) → range 2)
  (j : range n) := ∀ i x, fs i (flip x j) = NEG (fs i x)

lemma flippy_if_sensitive_f (p) {n m} (hm : m ≥ 3)
  (fs : range m → (range n → range 2) → range 2) (hfs : parity_poly p fs)
  {i j} (h : sensitive_f (fs i) j) :
  ∀ i' ≠ i, flippy_f (fs i') j := by
  intro i' hi' xi'
  obtain ⟨xi, hxi⟩ := h
  let xs (I : range m) (J : range n) : range 2 := complete p hm i' i (xi' J) (xi J) I
  let ys (I : range m) (J : range n) : range 2 :=
    if J = j then
      flip2 (xs · J) i' i I
    else
      xs I J
  have hxs J : Parity (xs · J) = p := by
    simp [xs]
    exact (complete_spec p hm hi' (xi' J) (xi J)).2
  have hys J : Parity (ys · J) = p := by
    by_cases J = j
    case pos hJ =>
      subst hJ
      simp [ys]
      apply hxs
    case neg hJ =>
      convert hxs J using 1
      simp [ys, hJ]
  let fxs i := fs i (xs i)
  let fys i := fs i (ys i)
  have hfxs : Parity fxs = p := hfs xs hxs
  have hfys : Parity fys = p := hfs ys hys
  by_contra! hxi'
  replace hxi' := NEG_of_ne hxi'
  simp at hxi'
  suffices Parity fys = NEG p by
    rw [hfys] at this
    apply NEG_ne p this
  suffices fys = flip fxs i by
    rw [this]
    simp
    rw [hfxs]
  funext I
  by_cases I = i
  case pos hI =>
    symm at hI
    subst hI
    have hx : xs i = xi := by
      simp [xs]
      funext J
      exact (complete_spec p hm hi' (xi' J) (xi J)).1.2
    have hyx : ys i = flip (xs i) j := by
      simp [xs, ys]
      funext J
      by_cases J = j
      case pos hJ =>
        subst hJ
        simp [flip2, flip, hi'.symm]
      case neg hJ =>
        simp [hJ, flip]
    simp [fxs, fys]
    rw [hyx, hx, hxi, flip]
    simp [hx]
  case neg hIi =>
  by_cases I = i'
  case pos hI =>
    symm at hI
    subst hI
    have hx : xs i' = xi' := by
      simp [xs]
      funext J
      exact (complete_spec p hm hi' (xi' J) (xi J)).1.1
    have hyx : ys i' = flip (xs i') j := by
      simp [xs, ys]
      funext J
      by_cases J = j
      case pos hJ =>
        subst hJ
        simp [flip2, flip, hi']
      case neg hJ =>
        simp [hJ, flip]
    simp [fxs, fys]
    rw [hyx, hx, hxi', flip]
    simp [hx, hi']
  case neg hIi' =>
    have : ys I = xs I := by
      simp [xs, ys]
      funext J
      by_cases J = j
      case pos hJ =>
        subst hJ
        simp [flip2, flip, hIi, hIi']
      case neg hJ =>
        simp [hJ]
    simp [fys, fxs, flip, hIi, this]

lemma flippy_if_sensitive (p) {n m} (hm : m ≥ 3)
  (fs : range m → (range n → range 2) → range 2) (hfs : parity_poly p fs)
  {j} (h : sensitive fs j) : flippy fs j := by
  obtain ⟨i, hi⟩ := h
  intro i'
  by_cases i' = i
  case pos hi' =>
    symm at hi'
    subst hi'
    let i' := other_ix hm i i
    have hi' := (other_ix_spec hm i i).1
    have : flippy_f (fs i') j := by
      apply flippy_if_sensitive_f <;> assumption
    have : sensitive_f (fs i') j := by
      use (fun _ => b0)
      apply this
    apply flippy_if_sensitive_f p hm fs hfs this
    symm
    assumption
  case neg hi' =>
    apply flippy_if_sensitive_f <;> assumption

noncomputable def sensitiveJ {n m} (fs : range m → (range n → range 2) → range 2) : Finset (range n) :=
  {j | sensitive fs j}

def char_fun {n} (S : Finset (range n)) (j : range n) : range 2 :=
  if j ∈ S then b1 else b0

lemma parity_poly_formula (p) {n m} (hm : m ≥ 3)
  (fs : range m → (range n → range 2) → range 2) (hfs : parity_poly p fs)
  (i : range m) : fs i = XOR (sensitiveJ fs) (fs i (fun _ => b0)) := by
  let b := fs i (fun _ => b0)
  suffices ∀ (S : Finset (range n)), fs i (char_fun S) = XOR (sensitiveJ fs) b (char_fun S) by
    funext x
    let S : Finset (range n) := {j | x j = b1 }
    have hS : x = char_fun S := by
      funext j
      simp [char_fun, S]
      cases of_range_2B (x j)
      case inl h => simp [h, b0, b1]
      case inr h => simp [h]
    rw [hS]
    apply this
  intro S
  induction S using Finset.induction
  case empty =>
    have hempty : char_fun ∅ = (fun _ => b0 : range n → range 2) := by
      funext j
      simp [char_fun]
    simp [hempty, XOR, b0, b]
    apply Subtype.coe_eq_of_eq_mk
    refine Eq.symm (Nat.mod_eq_of_lt ?_)
    apply mem_range.mp
    apply coe_mem
  case insert j T hj hT =>
    have hinsert : char_fun (insert j T) = flip (char_fun T) j := by
      funext J
      simp [char_fun, flip]
      by_cases J = j
      case pos hJ =>
        subst hJ
        simp [hj, NEG]
      case neg hJ =>
        simp [hJ]
    rw [hinsert]
    by_cases j ∈ sensitiveJ fs
    case pos hjs =>
      have hjs' : flippy fs j := by
        apply flippy_if_sensitive p hm fs hfs
        simp [sensitiveJ] at hjs
        exact hjs
      rw [hjs' i (char_fun T), hT]
      rw [XOR_flip_in]
      exact hjs
    case neg hjs =>
      rw [XOR_flip_notin]
      case h => exact hjs
      rw [←hT]
      symm
      contrapose! hjs
      replace hjs := NEG_of_ne hjs
      simp [sensitiveJ]
      use i, char_fun T
      simp [hjs]

lemma parity_polymorphisms_only_if' (p) {n m} (hm : m ≥ 3)
  (fs : range m → (range n → range 2) → range 2) (hfs : parity_poly p fs) :
  ∃ J, ∃ (b : range m → range 2),
    ∑ i : range m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range m), fs i = XOR J (b i) := by
  use sensitiveJ fs
  use fun i ↦ fs i (fun _ => b0)
  have h i := parity_poly_formula p hm fs hfs i
  constructor
  case right => exact h
  case left =>
    let xs (i : range m) (j : range n) := if i.val = 0 then p else b0
    have hxs j : Parity (xs · j) = p := by
      simp [xs, Parity]
      apply Subtype.coe_eq_of_eq_mk
      simp
      have : AtLeast3 m := ⟨hm⟩
      calc
        (∑ i : range m, (if i.val = 0 then p else b0).val) % 2 =
        (∑ i ∈ (range m).attach.erase range_0, 0 + p) % 2 := by
          congr
          simp
          have : range_0 ∈ (range m).attach := by simp
          rw [←sum_erase_add _ _ this]
          simp [range_0, b0]
          intro i hi hi'
          simp [hi']
        _ = p % 2 := by
          congr
          rw [sum_eq_zero, zero_add]
          intro i hi; rfl
        _ = p := by
          have := mem_range.mp p.property
          omega
    have hp := hfs xs hxs
    simp [Parity] at hp
    replace hp := congrArg (fun x => x.val) hp
    simp at hp
    have : AtLeast3 m := ⟨hm⟩
    replace hp := calc
      p = (∑ i ∈ (range m).attach, (fs i (xs i)).val) % 2 := by
        rw [hp]
      _ = (∑ i ∈ (range m).attach.erase range_0, (fs i (xs i)).val + (fs range_0 (xs range_0)).val) % 2 := by
        rw [sum_erase_add]
        simp
      _ = (∑ i ∈ (range m).attach.erase range_0, (fs i (fun _ ↦ b0)).val + (fs range_0 (fun _ ↦ p)).val) % 2 := by
        simp [xs, range_0]
        congr 2
        apply sum_congr rfl
        intro i hi
        congr
        funext j
        have : i.val ≠ 0 := by
          have := (mem_erase.mp hi).left
          contrapose! this
          apply Subtype.coe_eq_of_eq_mk
          exact this
        simp [this]
    have : fs range_0 (fun x ↦ p) = (fs range_0 (fun x ↦ b0) + #(sensitiveJ fs) * p) % 2 := by
      rw [h range_0, XOR, XOR]
      simp
      congr 1
      simp [b0, add_comm]
    rw [this] at hp
    norm_num at hp
    rw [←add_assoc, sum_erase_add] at hp
    case h => simp
    simp [Nat.ModEq]
    calc
      (∑ i : range m, (fs i (fun _ ↦ b0)).val) % 2 =
      (∑ i : range m, (fs i (fun _ ↦ b0)).val + 2*(#(sensitiveJ fs)*p)) % 2 := by
        omega
      _ = (∑ i : range m, (fs i (fun _ ↦ b0)).val + #(sensitiveJ fs)*p + #(sensitiveJ fs)*p) % 2 := by
        omega
      _ = (p + #(sensitiveJ fs)*p) % 2 := by
        nth_rewrite 3 [hp]
        norm_num
      _ = (#(sensitiveJ fs) + 1) * p % 2 := by
        congr
        ring

lemma parity_polymorphisms_only_if {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  {n} (poly : PolymorphismB P n) :
  ∃ J, ∃ (b : range P.m → range 2),
    ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range P.m), poly.fs i = XOR J (b i) := by
  obtain ⟨Pm, PP⟩ := parity_def' h
  symm at Pm
  subst Pm
  apply parity_polymorphisms_only_if' p hm
  intro xs hxs
  apply (PP _).mp
  apply poly.app xs
  intro j
  apply (PP _).mpr
  apply hxs

lemma parity_polymorphisms {P m p hm} (h : P = P_of_S (parity m p hm).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  ∃ J, ∃ (b : range P.m → range 2),
    ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range P.m), fs i = XOR J (b i)
  := by
  obtain ⟨Pm, PP⟩ := parity_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    obtain ⟨J, b, hb, hfs⟩ := parity_polymorphisms_only_if h poly
    use J, b
    constructor
    exact hb
    convert hfs with i
    exact hpoly.symm
  case mpr =>
    rintro ⟨J, b, hb, hfs⟩
    convert parity_polymorphisms_if h n J b hb with poly i
    exact hfs i

end NontrivialType
