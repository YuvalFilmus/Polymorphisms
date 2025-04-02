import Polymorphisms.SymmetricClassify
import Polymorphisms.SymmetricClassifyParity
import Polymorphisms.SymmetricClassifyAtmost
import Polymorphisms.SymmetricClassifyAtmost_m
import Polymorphisms.SymmetricClassifyTrivial
open Finset NontrivialType

def is_symmetricB (P : PredicateB) := ∃ S, P = P_of_S S

def is_polymorphism (P : PredicateB)
  {n} (fs : range P.m → (range n → range 2) → range 2) :=
  ∃ poly : PolymorphismB P n, poly.fs = fs

inductive SymmetricType where
  | nontrivial (nt : NontrivialType)
  | trivial_complement_closed
  | trivial_not_complement_closed

noncomputable def symmetric_type (P : PredicateB) : SymmetricType := by
  by_cases ∃ nt : NontrivialType, P = nt.denotationP
  case pos h =>
    use .nontrivial h.choose
  case neg =>
  by_cases complement_closed P
  case pos => use .trivial_complement_closed
  case neg => use .trivial_not_complement_closed

noncomputable def polymorphism_condition_nt (P : PredicateB) (nt : NontrivialType)
  {n} (fs : range P.m → (range n → range 2) → range 2) :=
  match nt with
  | .odd2 => ∀ x, fs range_1 x = NEG (fs range_0 (NEG_vec x))
  | .equal _ _ => ∀ i, fs i = fs (range_0)
  | .parity _ p _ =>
    ∃ J, ∃ (b : range P.m → range 2),
    ∑ i : range P.m, (b i).val ≡ (#J + 1) * p [MOD 2] ∧
    ∀ (i : range P.m), fs i = XOR J (b i)
  | .atmost _ w b _ _ =>
    ∀ (xs : range P.m → (range n → range 2)) (I : Finset (range P.m)), #I = w+1 →
    (∀ i ∈ I, fs i (xs i) = b) → ∃ j, ∀ i ∈ I, xs i j = b
  | .atmost_m m w b _ _ =>
    (∃ (J : Finset (range n)), ∀ i, fs i = AND' J b) ∨
    (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, fs i = CONST (NEG b))

noncomputable def polymorphism_condition (P : PredicateB)
  {n} (fs : range P.m → (range n → range 2) → range 2) :=
  match symmetric_type P with
  | .nontrivial nt =>
    polymorphism_condition_nt P nt fs
  | .trivial_complement_closed =>
    (∃ j, ∀ i x, fs i x = x j) ∨ (∃ j, ∀ i x, fs i x = NEG (x j)) ∨
      ∃ c : CertificateB P, ∀ (i : c.dom) x, fs i.1 x = c.ρ i
  | .trivial_not_complement_closed =>
    (∃ j, ∀ i x, fs i x = x j) ∨
      ∃ c : CertificateB P, ∀ (i : c.dom) x, fs i.1 x = c.ρ i

theorem symmetric_polymorphisms {P} (hP : is_symmetricB P)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  is_polymorphism P fs ↔ polymorphism_condition P fs
  := by
  obtain ⟨S, hS⟩ := hP
  unfold is_polymorphism
  unfold polymorphism_condition
  cases hst : symmetric_type P
  case nontrivial nt =>
    simp [hst]
    have h : P = P_of_S nt.denotation := by
      simp [symmetric_type] at hst
      split at hst
      case isTrue h =>
        simp at hst
        rw [←hst]
        exact h.choose_spec
      split at hst
      simp at hst
      simp at hst
    unfold polymorphism_condition_nt
    cases hnt : nt
    case odd2 =>
      simp only [hnt]
      apply odd2_polymorphisms
      simp [h, hnt]
    case equal m hm =>
      simp only [hnt]
      apply equal_polymorphisms
      simp [h, hnt]
      rfl
    case parity m p hm =>
      simp only [hnt]
      apply parity_polymorphisms
      simp [h, hnt]
      rfl
    case atmost m w b hm hw =>
      simp only [hnt]
      apply atmost_polymorphisms
      simp [h, hnt]
      rfl
    case atmost_m m w b hm hw =>
      simp only [hnt]
      apply atmost_m_polymorphisms
      simp [h, hnt]
      assumption
      assumption
  case trivial_complement_closed =>
    have hnt : ¬ ∃ nt : NontrivialType, P = nt.denotationP := by
      contrapose! hst
      unfold symmetric_type
      split; simp; simp
    have hclosed : complement_closed P := by
      contrapose! hst
      unfold symmetric_type
      split; simp; simp
    split; contradiction
    apply trivial_complement_closed_polymorphisms hS ?_ hclosed
    contrapose! hnt
    obtain ⟨nt, hnt⟩ := hnt
    use nt
    rw [denotationP, hnt, hS]
    contradiction
  case trivial_not_complement_closed =>
    have hnt : ¬ ∃ nt : NontrivialType, P = nt.denotationP := by
      contrapose! hst
      unfold symmetric_type
      split; simp; simp
    have hnot_closed : ¬ complement_closed P := by
      contrapose! hst
      unfold symmetric_type
      split; simp; simp
    split; contradiction; contradiction
    apply trivial_not_complement_closed_polymorphisms hS ?_ hnot_closed
    contrapose! hnt
    obtain ⟨nt, hnt⟩ := hnt
    use nt
    rw [denotationP, hnt, hS]
