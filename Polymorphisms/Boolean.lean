-- in this file we generalize the standard definitions to the Boolean case

import Polymorphisms.Basic
open Finset

def b0 : range 2 := ⟨0, by simp⟩
def b1 : range 2 := ⟨1, by simp⟩

lemma of_range_2B (b : range 2) : b = b0 ∨ b = b1 := of_range_2 b

lemma b1_of_not_b0 {b} (hb : b ≠ b0) : b = b1 := by
  cases of_range_2B b
  case inl h => subst h; contradiction
  case inr h => exact h

lemma b0_of_not_b1 {b} (hb : b ≠ b1) : b = b0 := by
  cases of_range_2B b
  case inr h => subst h; contradiction
  case inl h => exact h

def is_boolean (pred : Predicate) :=
  ∀ i, pred.a i = 2

-- non-degenerate predicate
@[ext]
structure PredicateB where
  -- arity of predicate
  m : ℕ
  hm : m ≥ 1
  -- predicate itself
  P : ((i : range m) → range 2) → Prop
  -- restrictions are full
  full (i : range m) (σ : range 2) : ∃ x, P x ∧ x i = σ
  -- depends on all coordinates
  dep (i : range m) : ∃ x y, P x ∧ ¬ P y ∧ ∀ i' ≠ i, x i' = y i'

def Predicate_of_PredicateB (pred : PredicateB) : Predicate :=
{
  m := pred.m,
  hm := pred.hm,
  a _ := 2,
  ha i := by simp,
  P := pred.P,
  full := pred.full,
  dep := pred.dep
}

lemma Predicate_of_PredicateB_boolean (pred : PredicateB) :
  is_boolean (Predicate_of_PredicateB pred) := by
  intro i
  simp [Predicate_of_PredicateB]

def vector_fromB {t : Type} {a : t → ℕ} (ha : ∀ i, a i = 2)
  (x : t → range 2) (i : t) : range (a i) :=
  ⟨x i, by apply mem_range.mpr; rw [ha i]; exact mem_range.mp (x i).2⟩

def vector_toB {t : Type} {a : t → ℕ} (ha : ∀ i, a i = 2)
  (x : (i : t) → range (a i)) (i : t) : range 2 :=
  ⟨x i, by apply mem_range.mpr; rw [←ha i]; exact mem_range.mp (x i).2⟩

def PredicateB_of_Predicate {pred : Predicate}
  (hpred : is_boolean pred) : PredicateB :=
{
  m := pred.m,
  hm := pred.hm,
  P x := pred.P (vector_fromB hpred x),
  full i σ := by
    let σ' : range (pred.a i) := ⟨σ.1, by
      apply mem_range.mpr
      rw [hpred i]
      apply mem_range.mp
      exact σ.2
    ⟩
    obtain ⟨x, Px, hx⟩ := pred.full i σ'
    use (vector_toB hpred x)
    constructor
    convert Px
    simp [vector_toB]
    aesop
  dep i := by
    obtain ⟨x, y, Px, nPy, h⟩ := pred.dep i
    use vector_toB hpred x, vector_toB hpred y
    constructor
    convert Px
    constructor
    convert nPy
    intro i' hi'
    simp [vector_toB]
    have := h i' hi'
    aesop
}

@[simp]
lemma PredicateB_of_Predicate_of_PredicateB (pred : PredicateB) :
  PredicateB_of_Predicate (Predicate_of_PredicateB_boolean pred) = pred := by
  unfold PredicateB_of_Predicate
  simp [Predicate_of_PredicateB]
  rfl

-- polymorphism
@[ext]
structure PolymorphismB (pred : PredicateB) (n : ℕ) where
  -- functions
  fs : (i : range pred.m) → (range n → range 2) → range 2
  -- polymorphicity
  app (xs : (i : range pred.m) → range n → range 2)
    (sat : ∀ j : range n, pred.P (xs · j)) :
    pred.P (fun i => fs i (xs i))

def Polymorphism_of_PolymorphismB {pred : PredicateB} {n : ℕ}
  (poly : PolymorphismB pred n) : Polymorphism (Predicate_of_PredicateB pred) n :=
{
  fs i x := poly.fs i x,
  app xs sat := by
    apply poly.app xs sat
}

def scalar_fromB {a : ℕ} (ha : a = 2) (x : range 2) : range a :=
  ⟨x, by apply mem_range.mpr; rw [ha]; exact mem_range.mp x.2⟩

def scalar_toB {a : ℕ} (ha : a = 2) (x : range a) : range 2 :=
  ⟨x, by apply mem_range.mpr; rw [←ha]; exact mem_range.mp x.2⟩

def vector_fromB' {t : Type} {a : ℕ} (ha : a = 2)
  (x : t → range 2) (i : t) : range a :=
  ⟨x i, by apply mem_range.mpr; rw [ha]; exact mem_range.mp (x i).2⟩

def vector_toB' {t : Type} {a : ℕ} (ha : a = 2)
  (x : t → range a) (i : t) : range 2 :=
  ⟨x i, by apply mem_range.mpr; rw [←ha]; exact mem_range.mp (x i).2⟩

def vectors_fromB {t t' : Type} {a : t → ℕ} (ha : ∀ i, a i = 2)
  (x : t → t' → range 2) (i : t) (j : t') : range (a i) :=
  ⟨x i j, by apply mem_range.mpr; rw [ha i]; exact mem_range.mp (x i j).2⟩

def vectors_toB {t t' : Type} {a : t → ℕ} (ha : ∀ i, a i = 2)
  (x : (i : t) → t' → range (a i)) (i : t) (j : t') : range 2 :=
  ⟨x i j, by apply mem_range.mpr; rw [←ha i]; exact mem_range.mp (x i j).2⟩

def Polymorphism_of_PolymorphismB' {pred : Predicate} (hpred : is_boolean pred) {n : ℕ}
  (poly : PolymorphismB (PredicateB_of_Predicate hpred) n) : Polymorphism pred n :=
{
  fs i x := scalar_fromB (hpred i) (poly.fs i (vector_toB' (hpred i) x)),
  app xs sat := by
    apply poly.app (vectors_toB hpred xs)
    intro j
    convert sat j
}

def PolymorphismB_of_Polymorphism {pred : Predicate} (hpred : is_boolean pred)
  {n} (poly : Polymorphism pred n) : PolymorphismB (PredicateB_of_Predicate hpred) n :=
{
  fs i x := scalar_toB (hpred i) (poly.fs i (vector_fromB' (hpred i) x)),
  app xs sat := by
    apply poly.app (vectors_fromB hpred xs)
    intro j
    convert sat j
}

@[simp]
lemma PolymorphismB_of_Polymorphism_of_PolymorphismB {pred n} (poly : PolymorphismB pred n) :
  PolymorphismB_of_Polymorphism (Predicate_of_PredicateB_boolean pred) (Polymorphism_of_PolymorphismB poly) = poly := by
  simp [PolymorphismB_of_Polymorphism, Polymorphism_of_PolymorphismB]
  ext i x
  simp [scalar_toB]
  unfold vector_fromB'
  rfl

@[simp]
lemma Polymorphism_of_PolymorphismB_of_Polymorphism {pred n} (hpred : is_boolean pred) (poly : Polymorphism pred n) :
  Polymorphism_of_PolymorphismB' hpred (PolymorphismB_of_Polymorphism hpred poly) = poly := by
  simp [Polymorphism_of_PolymorphismB', PolymorphismB_of_Polymorphism]
  ext i x
  simp [scalar_toB, scalar_fromB]
  unfold vector_fromB' vector_toB'
  rfl

-- certificate
@[ext]
structure CertificateB (pred : PredicateB) where
  -- domain
  dom : Set (range pred.m)
  -- the restriction
  ρ : (i : dom) → range 2
  -- being a certificate
  cert (x : (i : range pred.m) → range 2)
    (hx : ∀ i : dom, x i = ρ i) : pred.P x

def Certificate_of_CertificateB {pred : PredicateB}
  (c : CertificateB pred) : Certificate (Predicate_of_PredicateB pred) :=
{
  dom := c.dom,
  ρ i := c.ρ i,
  cert := c.cert
}

def CertificateB_of_Certificate {pred : Predicate} (hpred : is_boolean pred)
  (c : Certificate pred) : CertificateB (PredicateB_of_Predicate hpred) :=
{
  dom := c.dom,
  ρ i := scalar_toB (hpred i.1) (c.ρ i),
  cert x hx := by
    apply c.cert (vector_fromB hpred x)
    · intro i
      simp [vector_fromB]
      have := hx i
      simp [scalar_toB] at this
      aesop
}

lemma dom_nonemptyB {pred : PredicateB} (c : CertificateB pred) :
  ∃ i, i ∈ c.dom := by
  obtain ⟨i, hi⟩ := dom_nonempty (Certificate_of_CertificateB c)
  use i, hi

-- type of dictator
def formatB (pred : PredicateB) := (i : range pred.m) → range 2 → range 2

def format_of_formatB {pred : PredicateB} (φ : formatB pred) :
  format (Predicate_of_PredicateB pred) :=
  fun i => fun σ => φ i σ

def formatB_of_format {pred : Predicate} (hpred : is_boolean pred)
  (φ : format pred) : formatB (PredicateB_of_Predicate hpred) :=
  fun i => fun σ => scalar_toB (hpred i) (φ i (scalar_fromB (hpred i) σ))

def formats_of_formatsB {pred : PredicateB} (Φ : Set (formatB pred)) :
  Set (format (Predicate_of_PredicateB pred)) :=
  Set.image (@format_of_formatB pred) Φ

def formatsB_of_formats {pred : Predicate} (hpred : is_boolean pred)
  (Φ : Set (format pred)) : Set (formatB (PredicateB_of_Predicate hpred)) :=
  Set.image (formatB_of_format hpred) Φ

@[simp]
lemma formatsB_of_formats_of_formatsB {pred : PredicateB} (Φ : Set (formatB pred)) :
  formatsB_of_formats (Predicate_of_PredicateB_boolean pred) (formats_of_formatsB Φ) = Φ := by
  simp [formats_of_formatsB, formatsB_of_formats]
  exact Function.LeftInverse.image_image (congrFun rfl) Φ

lemma format_in_of_formatB_in {pred : PredicateB}
  {φ : formatB pred} {Φ : Set (formatB pred)}
  (h : φ ∈ Φ) : (format_of_formatB φ) ∈ (formats_of_formatsB Φ) := by
  unfold formats_of_formatsB
  apply Set.mem_image_of_mem
  exact h

lemma formatB_in_of_format_in {pred : Predicate} (hpred : is_boolean pred)
  {φ : format pred} {Φ : Set (format pred)}
  (h : φ ∈ Φ) : (formatB_of_format hpred φ) ∈ (formatsB_of_formats hpred Φ) := by
  unfold formatsB_of_formats
  apply Set.mem_image_of_mem
  assumption

-- polymorphism of dictatorship type
def is_dictatorshipB {pred : PredicateB} {n : ℕ} (poly : PolymorphismB pred n) (Φ : Set (formatB pred)) :=
  ∃ j : range n, ∃ φ ∈ Φ, ∀ i : range pred.m, ∀ x : range n → range 2, poly.fs i x = φ i (x j)

lemma is_dictatorship_of_is_dictatorshipB {pred n} {poly : PolymorphismB pred n} {Φ}
  (hdict : is_dictatorshipB poly Φ) : is_dictatorship (Polymorphism_of_PolymorphismB poly) (formats_of_formatsB Φ) := by
  obtain ⟨j, φ, hφ, h⟩ := hdict
  use j, format_of_formatB φ, format_in_of_formatB_in hφ
  intro i x
  convert h i x

lemma is_dictatorshipB_of_is_dictatorship {pred n} (hpred : is_boolean pred) {poly : Polymorphism pred n} {Φ}
  (hdict : is_dictatorship poly Φ) : is_dictatorshipB (PolymorphismB_of_Polymorphism hpred poly) (formatsB_of_formats hpred Φ) := by
  obtain ⟨j, φ, hφ, h⟩ := hdict
  use j, formatB_of_format hpred φ, formatB_in_of_format_in hpred hφ
  intro i x
  have := h i (vector_fromB' (hpred i) x)
  simp [PolymorphismB_of_Polymorphism, scalar_toB, formatB_of_format, scalar_fromB]
  rw [this]
  unfold vector_fromB'
  rfl

-- polymorphism of certificate type
def is_certificateB {pred : PredicateB} {n : ℕ} (poly : PolymorphismB pred n) :=
  ∃ c : CertificateB pred, ∀ i : c.dom, ∀ x : range n → range 2, poly.fs i x = c.ρ i

lemma is_certificate_of_is_certificateB {pred n} {poly : PolymorphismB pred n}
  (hcert : is_certificateB poly) : is_certificate (Polymorphism_of_PolymorphismB poly) := by
  obtain ⟨c, hc⟩ := hcert
  use Certificate_of_CertificateB c
  intro i x
  apply hc i x

lemma is_certificateB_of_is_certificate {pred n} (hpred : is_boolean pred) {poly : Polymorphism pred n}
  (hcert : is_certificate poly) : is_certificateB (PolymorphismB_of_Polymorphism hpred poly) := by
  obtain ⟨c, hc⟩ := hcert
  use CertificateB_of_Certificate hpred c
  intro i x
  have := hc i (vector_fromB' (hpred i.1) x)
  simp [PolymorphismB_of_Polymorphism, CertificateB_of_Certificate, scalar_toB]
  rw [this]

-- triviality for a specific value of n
def trivial_forB (pred : PredicateB) (Φ : Set (formatB pred)) (n : ℕ) :=
  ∀ poly : PolymorphismB pred n, is_dictatorshipB poly Φ ∨ is_certificateB poly

lemma trivial_for_of_trivial_forB {pred : PredicateB} {Φ : Set (formatB pred)} {n : ℕ}
  (htrivial : trivial_forB pred Φ n) : trivial_for (Predicate_of_PredicateB pred) (formats_of_formatsB Φ) n := by
  intro poly
  cases htrivial (PolymorphismB_of_Polymorphism (Predicate_of_PredicateB_boolean pred) poly)
  case inl hdict =>
    left
    convert is_dictatorship_of_is_dictatorshipB hdict
  case inr hcert =>
    right
    convert is_certificate_of_is_certificateB hcert

lemma trivial_forB_of_trivial_for {pred : Predicate} (hpred : is_boolean pred) {Φ : Set (format pred)} {n : ℕ}
  (htrivial : trivial_for pred Φ n) : trivial_forB (PredicateB_of_Predicate hpred) (formatsB_of_formats hpred Φ) n := by
  intro poly
  cases htrivial (Polymorphism_of_PolymorphismB' hpred poly)
  case inl hdict =>
    left
    convert is_dictatorshipB_of_is_dictatorship hpred hdict
  case inr hcert =>
    right
    convert is_certificateB_of_is_certificate hpred hcert

-- all formats are composed of permutations
def permutationalB {pred : PredicateB} (Φ : Set (formatB pred)) :=
  ∀ φ ∈ Φ, ∀ i : range pred.m, Function.Bijective (φ i)

def permutational_of_permutationalB {pred : PredicateB}
  {Φ : Set (formatB pred)} (hperm : permutationalB Φ) :
  permutational (formats_of_formatsB Φ) := by
  intro φ hφ
  simp [formats_of_formatsB] at hφ
  obtain ⟨φB, hφB, hconv⟩ := hφ
  symm at hconv
  subst hconv
  intro i
  let iB : range pred.m := ⟨i, by simp [Predicate_of_PredicateB]⟩
  convert hperm φB hφB iB

-- special case of n = 1

-- polymorphism
@[ext]
structure Polymorphism₁B (pred : PredicateB) where
  -- functions
  fs _ (σ : range 2) : range 2
  -- polymorphicity
  app : ∀ y, pred.P y → pred.P (fun i => fs i (y i))

-- polymorphism of dictatorship type
def is_dictatorship₁B {pred : PredicateB} (poly : Polymorphism₁B pred) (Φ : Set (formatB pred)) :=
  poly.fs ∈ Φ

-- polymorphism of certificate type
def is_certificate₁B {pred : PredicateB} (poly : Polymorphism₁B pred) :=
  ∃ c : CertificateB pred, ∀ i : c.dom, poly.fs i = fun _ => c.ρ i

-- triviality for n = 1
def trivial_for₁B (pred : PredicateB) (Φ : Set (formatB pred)) :=
  ∀ poly : Polymorphism₁B pred, is_dictatorship₁B poly Φ ∨ is_certificate₁B poly

lemma trivial_for_1_iff_trivial_for₁B (pred : PredicateB) (Φ : Set (formatB pred)) :
  trivial_forB pred Φ 1 ↔ trivial_for₁B pred Φ := by
  constructor
  case mp =>
    intro htrivial poly₁
    let poly : PolymorphismB pred 1 :=
    {
      fs i x := poly₁.fs i (x range_0),
      app xs sat := by
        let y i := xs i range_0
        have := poly₁.app y (sat range_0)
        simp [y] at this
        simpa
    }
    cases htrivial poly
    case inl hdict =>
      left
      obtain ⟨j, φ, hφ, hf⟩ := hdict
      have hj := of_range_1 j
      unfold is_dictatorship₁B
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
    let poly₁ : Polymorphism₁B pred :=
    {
      fs i σ := poly.fs i (fun _ => σ),
      app y Py := by
        let xs i := (fun _ : range 1 => y i)
        have := poly.app xs (by intro; exact Py)
        simp [xs] at this
        simp
        assumption
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
