-- in this file we prove the main theorem regarding symmetric Boolean predicates

import Polymorphisms.BooleanReductions
import Polymorphisms.BooleanAux
import Polymorphisms.SymmetricDefs
import Polymorphisms.SymmetricIf
import Polymorphisms.SymmetricOnlyIf
import Polymorphisms.SymmetricOnlyIfMonotone

lemma symmetric_classification_if (t : Φ_type) (S : SymmetricB)
  (h : ∀ n, trivial_forB (P_of_S S) (Φ_std t S) n) :
  (¬ is_nontrivial_S S ∧ (is_comp_closed S → t = .neg)) := by
  contrapose! h
  by_cases is_nontrivial_S S
  case pos h =>
    cases h
    case inl heven =>
      obtain ⟨m, hm, hS⟩ := heven
      subst hS
      apply S_even_nontrivial
    case inr h =>
    cases h
    case inl hodd =>
      obtain ⟨m, hm, hS⟩ := hodd
      subst hS
      apply S_odd_nontrivial
    case inr h =>
    cases h
    case inl hatmost =>
      obtain ⟨m, b, hlb, hub, hS⟩ := hatmost
      subst hS
      apply S_atmost_nontrivial
    case inr h =>
    cases h
    case inl hatleast =>
      obtain ⟨m, b, hlb, hub, hS⟩ := hatleast
      subst hS
      apply S_atleast_nontrivial
    case inr h =>
    cases h
    case inl hatmost_m =>
      obtain ⟨m, b, hub, hS⟩ := hatmost_m
      subst hS
      apply S_atmost_m_nontrivial
    case inr hatleast_0 =>
      obtain ⟨m, b, hlb, hub, hS⟩ := hatleast_0
      subst hS
      apply S_atleast_0_nontrivial
  case neg htrivial =>
    obtain ⟨ht, hcomp_closed⟩ := h htrivial
    replace hcomp_closed : t = Φ_type.id := by
      cases t <;> simp
      contradiction
    simp [Φ_std, ht, hcomp_closed]
    use 1
    have := S_comp_closed_nontrivial ht
    contrapose! this
    apply (trivial_for_1_iff_trivial_for₁B _ _).mp
    assumption

lemma symmetric_classification_only_if (t : Φ_type) (S : SymmetricB)
  (h : ¬ is_nontrivial_S S ∧ (is_comp_closed S → t = .neg)) :
  ∀ n, trivial_forB (P_of_S S) (Φ_std t S) n := by
  apply (trivial_iff_trivial_for_2B _ _).mpr
  contrapose! h
  suffices is_nontrivial_S S ∨ (is_comp_closed S ∧ ((fun _ => NEG) ∉ (Φ_std t S))) by
    cases this
    case inl h =>
      intro h'
      contradiction
    case inr h =>
      intro _
      constructor
      · exact h.1
      cases ht : t
      case id => simp
      case neg =>
      subst ht
      replace h := h.2
      contrapose! h
      simp [Φ_std, Φ_neg]
      apply Set.mem_setOf.mpr
      intro _ _
      right
      simp
  by_cases trivial_for₁B (P_of_S S) (Φ_std t S)
  case neg h₁ =>
    cases not_trivial_for_1B h₁
    case inl h₁ =>
      left
      exact nontrivial_if_has_monotone_counterexample h₁
    case inr h₁ =>
      exact nontrivial_if_has_nonconst_counterexample (Φ_std t S) (Φ_std_contains_ID t S) h₁
  case pos h₁ =>
    cases trivial_for_2_of_trivial_for_1B (Φ_std_perm _ _) h₁
    case inl h => contradiction
    case inr h =>
    cases h
    case inl hclosure =>
      left
      exact nontrivial_if_has_closureB hclosure
    case inr h =>
    cases h
    case inl hANDOR =>
      left
      exact nontrivial_if_has_AND_OR_polyB hANDOR
    case inr hLatin =>
      left
      exact nontrivial_if_has_Latin_square_polyB (Φ_std_perm _ _) hLatin

theorem symmetric_classification (t : Φ_type) (S : SymmetricB) :
  (∀ n, trivial_forB (P_of_S S) (Φ_std t S) n) ↔
  (¬ is_nontrivial_S S ∧ (is_comp_closed S → t = .neg)) := by
  constructor
  · intro h
    apply symmetric_classification_if
    assumption
  · intro h
    apply symmetric_classification_only_if
    assumption
