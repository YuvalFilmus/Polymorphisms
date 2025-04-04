import Mathlib.Tactic

open Finset

-- non-degenerate predicate
@[ext]
structure Predicate where
  -- arity of predicate
  m : ℕ
  hm : m ≥ 1
  -- alphabet sizes
  a : range m → ℕ
  ha (i : range m) : a i ≥ 2
  -- predicate itself
  P : ((i : range m) → range (a i)) → Prop
  -- restrictions are full
  full (i : range m) (σ : range (a i)) : ∃ x, P x ∧ x i = σ
  -- depends on all coordinates
  dep (i : range m) : ∃ x y, P x ∧ ¬ P y ∧ ∀ i' ≠ i, x i' = y i'

-- polymorphism
@[ext]
structure Polymorphism (pred : Predicate) (n : ℕ) where
  -- functions
  fs : (i : range pred.m) → (range n → range (pred.a i)) → range (pred.a i)
  -- polymorphicity
  app (xs : (i : range pred.m) → range n → range (pred.a i))
    (sat : ∀ j : range n, pred.P (xs · j)) :
    pred.P (fun i => fs i (xs i))

-- certificate
@[ext]
structure Certificate (pred : Predicate) where
  -- domain
  dom : Set (range pred.m)
  -- the restriction
  ρ : (i : dom) → range (pred.a i)
  -- being a certificate
  cert (x : (i : range pred.m) → range (pred.a i))
    (hx : ∀ i : dom, x i = ρ i) : pred.P x

-- type of dictator
def format (pred : Predicate) := (i : range pred.m) → range (pred.a i) → range (pred.a i)

-- polymorphism of dictatorship type
def is_dictatorship {pred : Predicate} {n : ℕ} (poly : Polymorphism pred n) (Φ : Set (format pred)) :=
  ∃ j : range n, ∃ φ ∈ Φ, ∀ i : range pred.m, ∀ x : range n → range (pred.a i), poly.fs i x = φ i (x j)

-- polymorphism of certificate type
def is_certificate {pred : Predicate} {n : ℕ} (poly : Polymorphism pred n) :=
  ∃ c : Certificate pred, ∀ i : c.dom, ∀ x : range n → range (pred.a i), poly.fs i x = c.ρ i

-- triviality for a specific value of n
def trivial_for (pred : Predicate) (Φ : Set (format pred)) (n : ℕ) :=
  ∀ poly : Polymorphism pred n, is_dictatorship poly Φ ∨ is_certificate poly

-- all formats are composed of permutations
def permutational {pred : Predicate} (Φ : Set (format pred)) :=
  ∀ φ ∈ Φ, ∀ i : range pred.m, Function.Bijective (φ i)

-- type classes

class AtLeast1 (n : ℕ) where
  cond : n ≥ 1

class AtLeast2 (n : ℕ) where
  cond : n ≥ 2

class AtLeast3 (n : ℕ) where
  cond : n ≥ 3

instance : AtLeast1 1 :=
  ⟨by simp⟩

instance {n : ℕ} : AtLeast1 (n + 1) :=
  ⟨by simp⟩

instance : AtLeast2 2 :=
  ⟨by simp⟩

instance : AtLeast3 3 :=
  ⟨by simp⟩

instance {n : ℕ} [h : AtLeast2 n] : AtLeast1 n :=
  ⟨by linarith [h.cond]⟩

instance {n : ℕ} [h : AtLeast3 n] : AtLeast2 n :=
  ⟨by linarith [h.cond]⟩

instance {pred : Predicate} : AtLeast1 pred.m :=
  ⟨pred.hm⟩

instance {pred : Predicate} {i : range pred.m}: AtLeast2 (pred.a i) :=
  ⟨pred.ha i⟩

def range_0 {n : ℕ} [h : AtLeast1 n] : range n :=
  ⟨0, by simp; linarith [h.cond]⟩

def range_1 {n : ℕ} [h : AtLeast2 n] : range n :=
  ⟨1, by simp; linarith [h.cond]⟩

def range_2 {n : ℕ} [h : AtLeast3 n] : range n :=
  ⟨2, by simp; linarith [h.cond]⟩

instance {n} [AtLeast1 n] : OfNat (range n) 0 :=
  ⟨range_0⟩

instance {n} [AtLeast2 n] : OfNat (range n) 1 :=
  ⟨range_1⟩

instance {n} [AtLeast3 n] : OfNat (range n) 2 :=
  ⟨range_2⟩

@[simp]
lemma zero_neq_one {n} [AtLeast2 n] : (0 : range n) ≠ (1 : range n) := by
  intro h
  reduce at h
  simp at h

@[simp]
lemma one_ne_zero'' {n} [AtLeast2 n] : (1 : range n) ≠ (0 : range n) := by
  intro h
  reduce at h
  simp at h

def cons_input {a : ℕ} (σ₀ σ₁ : range a) (k : range 2) :=
  if k = range_0 then σ₀ else σ₁

def cons_input' {a : ℕ} (σ₀ σ₁ : range a) (k : range 2) :=
  if k = 0 then σ₀ else σ₁

lemma of_range_1 (k : range 1) : k = range_0 := by
  obtain ⟨val, prop⟩ := k
  simp [range_0]
  replace prop := mem_range.mp prop
  linarith [prop]

lemma of_range_2' {a} [AtLeast2 a] (ha : a = 2)
  (k : range a) : k = range_0 ∨ k = range_1 := by
  obtain ⟨val, prop⟩ := k
  simp [range_0, range_1]
  replace prop := mem_range.mp prop
  match val with
  | 0 => left; rfl
  | 1 => right; rfl
  | n+1+1 => exfalso; linarith [prop]

lemma of_range_2 (k : range 2) : k = range_0 ∨ k = range_1 :=
  of_range_2' (rfl) k

lemma of_range_2''' {a} [AtLeast2 a] (ha : a = 2)
  (k : range a) : k = 0 ∨ k = 1 := by
  obtain ⟨val, prop⟩ := k
  replace prop := mem_range.mp prop
  match val with
  | 0 => left; rfl
  | 1 => right; rfl
  | n+1+1 => exfalso; linarith [prop]

lemma of_range_2'' (k : range 2) : k = 0 ∨ k = 1 :=
  of_range_2''' (rfl) k

@[simp]
lemma cons_input_of_components {a : ℕ}
  (x : range 2 → range a) : cons_input (x range_0) (x range_1) = x := by
  funext k
  cases of_range_2 k
  all_goals simp [cons_input]
  case inl h => rw [h]; simp
  case inr h => rw [h]; simp [range_0, range_1]

@[simp]
lemma cons_input_of_components' {a : ℕ}
  (x : range 2 → range a) : cons_input' (x 0) (x 1) = x := by
  funext k
  cases of_range_2'' k
  all_goals simp [cons_input']
  case inl h => rw [h]; simp
  case inr h => rw [h]; simp

lemma dom_nonempty {pred : Predicate} (c : Certificate pred) :
  ∃ i, i ∈ c.dom := by
  by_contra h
  push_neg at h
  obtain ⟨_, y, _, notPy, _⟩ := pred.dep range_0
  apply notPy
  apply c.cert
  intro i
  exfalso
  apply h i
  exact i.prop

-- special case of n = 1

-- polymorphism
@[ext]
structure Polymorphism₁ (pred : Predicate) where
  -- functions
  fs i (σ : range (pred.a i)) : range (pred.a i)
  -- polymorphicity
  app : ∀ y, pred.P y → pred.P (fun i => fs i (y i))

-- polymorphism of dictatorship type
def is_dictatorship₁ {pred : Predicate} (poly : Polymorphism₁ pred) (Φ : Set (format pred)) :=
  poly.fs ∈ Φ

-- polymorphism of certificate type
def is_certificate₁ {pred : Predicate} (poly : Polymorphism₁ pred) :=
  ∃ c : Certificate pred, ∀ i : c.dom, poly.fs i = fun _ => c.ρ i

-- triviality for n = 1
def trivial_for₁ (pred : Predicate) (Φ : Set (format pred)) :=
  ∀ poly : Polymorphism₁ pred, is_dictatorship₁ poly Φ ∨ is_certificate₁ poly

lemma trivial_for_1_iff_trivial_for₁ (pred : Predicate) (Φ : Set (format pred)) :
  trivial_for pred Φ 1 ↔ trivial_for₁ pred Φ := by
  constructor
  case mp =>
    intro htrivial poly₁
    let poly : Polymorphism pred 1 :=
    {
      fs i x := poly₁.fs i (x range_0),
      app xs sat := by
        let y i := xs i range_0
        have := poly₁.app y (sat range_0)
        simp [y] at this
        simp
        assumption
    }
    cases htrivial poly
    case inl hdict =>
      left
      obtain ⟨j, φ, hφ, hf⟩ := hdict
      have hj := of_range_1 j
      unfold is_dictatorship₁
      convert hφ
      funext i
      funext σ
      have := hf i (fun _ => σ)
      simp [poly] at this
      assumption
    case inr hcert =>
      right
      obtain ⟨c, hc⟩ := hcert
      use c
      intro i
      funext σ
      have := hc i (fun _ => σ)
      simp [poly] at this
      assumption
  case mpr =>
    intro htrivial₁ poly
    let poly₁ : Polymorphism₁ pred :=
    {
      fs i σ := poly.fs i (fun _ => σ),
      app y Py := by
        let xs i := (fun _ : range 1 => y i)
        have := poly.app xs (by intro; exact Py)
        simp [xs] at this
        simpa
    }
    cases htrivial₁ poly₁
    case inl hdict =>
      left
      use range_0, poly₁.fs, hdict
      intro i x
      simp [poly₁, range_0]
      congr
      funext j
      congr
      apply of_range_1
    case inr hcert =>
      right
      obtain ⟨c, hc⟩ := hcert
      use c
      intro i x
      have := congr_fun (hc i) (x range_0)
      simp [poly₁] at this
      rw [←this]
      congr
      funext j
      congr
      apply of_range_1
