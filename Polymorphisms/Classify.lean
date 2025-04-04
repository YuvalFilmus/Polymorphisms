-- in this file we classify functions to constant and non-constant

import Polymorphisms.Basic
open Finset

section φ_classification

variable {a : ℕ} [AtLeast1 a]

inductive φ_type (a : ℕ)
| const (τ : range a)
| nonconst (σ₁ σ₂ : range a)

def φ_classify (φ : range a → range a) : φ_type a :=
  let nonequal : Finset _ := { σ | φ σ ≠ φ 0 }
  if h : nonequal.Nonempty then
    .nonconst 0 (min' nonequal h)
  else
    .const (φ 0)

lemma φ_const_spec (φ : range a → range a) (τ : range a) :
  φ_classify φ = .const τ ↔ ∀ σ : range a, φ σ = τ := by
  constructor
  · intro hclassify σ
    simp [φ_classify] at hclassify
    split at hclassify
    case isTrue => contradiction
    case isFalse hempty =>
      rw [φ_type.const.injEq] at hclassify
      rw [←hclassify]
      simp at hempty
      have := filter_eq_empty_iff.mp hempty (mem_univ σ)
      push_neg at this
      rw [this]
  · intro hφ
    simp [φ_classify]
    split
    case isTrue hnonempty =>
      simp [hnonempty]
      contrapose! hnonempty
      apply not_nonempty_iff_eq_empty.mpr
      apply filter_eq_empty_iff.mpr
      push_neg
      intro σ _
      rw [hφ σ, hφ 0]
    case isFalse hempty =>
      congr
      exact hφ 0

def φ_const (φ : range a → range a) :=
match φ_classify φ with
| .const _ => true
| .nonconst _ _ => false

lemma φ_classify_of_φ_const {φ : range a → range a}
  (h : φ_const φ = true) : φ_classify φ = .const (φ 0) := by
  cases hφ : φ_classify φ
  all_goals simp [φ_const, hφ] at h
  case const τ =>
    congr
    rw [(φ_const_spec φ τ).mp hφ]

lemma φ_classify_of_not_φ_const {φ : range a → range a}
  (h : φ_const φ = false) : ∃ σ₁ σ₂, φ_classify φ = .nonconst σ₁ σ₂ := by
  cases hφ : φ_classify φ
  all_goals simp [φ_const, hφ] at h
  case nonconst σ₁ σ₂ =>
    use σ₁, σ₂

lemma φ_nonconst_spec {φ : range a → range a} {σ₁ σ₂ : range a}
  (hclassify : φ_classify φ = .nonconst σ₁ σ₂):
  φ σ₁ ≠ φ σ₂ := by
  simp [φ_classify] at hclassify
  split at hclassify
  case isFalse => contradiction
  case isTrue hnonempty =>
  simp [hnonempty] at hclassify
  rw [←hclassify.1]
  have := (mem_filter.mp (min'_mem _ hnonempty)).2
  rw [hclassify.2] at this
  symm
  assumption

lemma φ_nonconst_spec' {φ : range a → range a} {σ₁ σ₂ : range a}
  (hφ : φ σ₁ ≠ φ σ₂) : ∃ σ₁ σ₂, φ_classify φ = .nonconst σ₁ σ₂ := by
  cases h : φ_classify φ with
  | const τ =>
    exfalso
    apply hφ
    replace h := (φ_const_spec φ τ).mp h
    rw [h σ₁, h σ₂]
  | nonconst σ₁ σ₂ =>
    use σ₁, σ₂

end φ_classification
