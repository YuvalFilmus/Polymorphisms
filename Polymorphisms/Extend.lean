-- in this file, we prove that if pred is Φ-trivial for some n
-- then it is also Φ-trivial for all smaller n

import Polymorphisms.Basic
open Finset

section extend

variable {pred : Predicate} {Φ : Set (format pred)} {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂)

-- extend an input
def extend_input {i : range pred.m} (x : range n₁ → range (pred.a i)) (j : range n₂) :=
  if hj : j < n₁ then
    x ⟨j, by simp [hj]⟩
  else
    range_0

-- extend an index
def extend_index (j : range n₁) : range n₂ :=
  ⟨j, by simp; linarith [mem_range.mp j.prop, hn]⟩

-- extend a function
def extend_function {i : range pred.m} (f : (range n₁ → range (pred.a i)) → range (pred.a i))
  (x : range n₂ → range (pred.a i)) : range (pred.a i) :=
  f (fun j => x (extend_index hn j))

-- evaluating extended function on extended input
@[simp]
def extend_eval {i : range pred.m} (f : (range n₁ → range (pred.a i)) → range (pred.a i))
  (x : range n₁ → range (pred.a i)) :
  (extend_function hn f) (extend_input x) = f x := by
  simp [extend_function, extend_input, extend_index]
  congr 1
  funext i
  simp [mem_range.mp i.prop]

-- extend a polymorphism
@[simp]
def extend_polymorphism (P : Polymorphism pred n₁) : Polymorphism pred n₂ :=
{
  fs i := extend_function hn (P.fs i),
  app xs sat := by
    let ys i := (fun j => xs i (extend_index hn j))
    apply P.app ys
    intro j
    apply sat (extend_index hn j)
}

-- predicate is non-empty
def predicate_nonempty :
  ∃ y, pred.P y := by
  rcases pred.dep range_0 with ⟨x, y, Px, _, _⟩
  use x

theorem trivial_of_trivial_larger (trivial : trivial_for pred Φ n₂) (hn : n₁ ≤ n₂):
  trivial_for pred Φ n₁ := by
  intro P
  cases trivial (extend_polymorphism hn P) with
  | inl hdictatorship =>
    rcases hdictatorship with ⟨j, φ, hφ, conforms⟩
    by_cases hj : j < n₁
    -- if j < n₁ then we are a dictatorship
    · left
      use ⟨j, by simp [hj]⟩, φ, hφ
      intro i x
      have := conforms i (extend_input x)
      simp [extend_input, hj] at this
      rw [←this]
    -- if j ≥ n then all functions are constant, so we are actually a certificate
    · right
      let ρ (i : range pred.m) := φ i range_0
      have hconst (i : range pred.m) (x : range n₁ → range (pred.a i)) :
        P.fs i x = ρ i := by
        calc
          P.fs i x = (extend_polymorphism hn P).fs i (extend_input x) := by simp
          _ = φ i range_0 := by
            rw [conforms i (extend_input x)]
            congr
            simp [extend_input, hj]
          _ = ρ i := rfl
      have Pρ : pred.P ρ := by
        rcases @predicate_nonempty pred with ⟨y, Py⟩
        let xs (i : range pred.m) (j : range n₁) := y i
        convert P.app xs _ with i
        · symm
          apply hconst
        · intro j
          simp [xs]
          exact Py
      use {
        dom := Set.univ,
        ρ i := ρ i,
        cert := by
          intro xs hxs
          convert Pρ
          funext i
          exact hxs ⟨i, by simp⟩
      }
      intro i x
      simp
      apply hconst
  | inr hcertificate =>
    rcases hcertificate with ⟨c, conforms⟩
    right
    use c
    intro i x
    rw [←conforms i (extend_input x)]
    simp

end extend
