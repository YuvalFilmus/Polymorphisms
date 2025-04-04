-- in this file, we define the operation of restricting a polymorphism

import Polymorphisms.Basic
open Finset

def range_last {n : ℕ} : range (n+1) :=
  ⟨n, by exact self_mem_range_succ n⟩

def extend_input_by {pred : Predicate} {i : range pred.m} {n : ℕ}
  (x : range n → range (pred.a i)) (σ : range (pred.a i)) (j : range (n + 1)) : range (pred.a i) :=
  if hj : j < n then
    x ⟨j, by simp; linarith [hj]⟩
  else
    σ

def shorten_input {pred : Predicate} {i : range pred.m} {n : ℕ}
  (x : range (n+1) → range (pred.a i)) (j : range n) :=
  x ⟨j, by apply mem_range.mpr; linarith [mem_range.mp j.coe_prop]⟩

@[simp]
def shorten_input_of_extend_input_by {pred : Predicate} {i : range pred.m} {n : ℕ}
  (x : range n → range (pred.a i)) (σ : range (pred.a i)) :
  shorten_input (extend_input_by x σ) = x := by
  unfold extend_input_by
  unfold shorten_input
  funext j
  simp [mem_range.mp j.coe_prop]

@[simp]
def extend_input_by_of_shorten_input {pred : Predicate} {i : range pred.m} {n : ℕ}
  (x : range (n+1) → range (pred.a i)) :
  extend_input_by (shorten_input x) (x range_last) = x := by
  unfold shorten_input
  unfold extend_input_by
  funext j
  split
  case isTrue =>
    simp
  case isFalse h =>
    simp [range_last]
    congr
    linarith [h, mem_range.mp j.coe_prop]

def restrict_polymorphism {pred : Predicate} {n : ℕ} (poly : Polymorphism pred (n + 1))
  {y} (Py : pred.P y) : Polymorphism pred n :=
{
  fs i x := poly.fs i (extend_input_by x (y i)),
  app xs sat := by
    let ys i := extend_input_by (xs i) (y i)
    apply poly.app ys
    intro j
    by_cases hj : j < n
    · simp [ys, extend_input_by, hj]
      apply sat
    · simp [ys, extend_input_by, hj]
      exact Py
}

def restrict_polymorphism₁ {pred : Predicate} (poly : Polymorphism pred 2)
  {y} (Py : pred.P y) : Polymorphism₁ pred :=
{
  fs i σ := poly.fs i (cons_input σ (y i)),
  app xs sat := by
    let ys i := cons_input (xs i) (y i)
    apply poly.app ys
    intro j
    cases of_range_2'' j
    case inl hj =>
      simp [ys, hj, cons_input]
      exact sat
    case inr hj =>
      simp [ys, hj, cons_input]
      apply Py
}
