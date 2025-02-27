import Mathlib.Tactic
open Finset

section

variable {α : Type} [hα : Inhabited α] [DecidableEq α]

lemma finset_to_range_bij' (s : Finset α) :
  ∃ _ : range #s ≃ s, True := by
  induction s using strongInduction
  case H s hind =>
  by_cases s = ∅
  case pos h =>
    have hs : #s = 0 := card_eq_zero.mpr h
    use {
      toFun i := ⟨hα.default, by have := mem_range.mp (coe_mem i); omega⟩
      invFun i := ⟨0, by have := coe_mem i; subst h; have := not_mem_empty i; contradiction⟩
      left_inv := by intro i; have := mem_range.mp (coe_mem i); omega
      right_inv := by intro i; have := coe_mem i; subst h; have := not_mem_empty i; contradiction
    }
  case neg h =>
    push_neg at h
    obtain ⟨x, hx⟩ := Nonempty.exists_mem (nonempty_of_ne_empty h)
    let t := s.erase x
    have ht : t ⊂ s := erase_ssubset hx
    have hcard : #s = #t + 1 := Eq.symm (card_erase_add_one hx)
    obtain ⟨e, _⟩ := hind t ht
    use {
      toFun n :=
        if h : n = #t then
          ⟨x, hx⟩
        else
          ⟨e ⟨n, by
            push_neg at h
            apply mem_range.mpr
            have := mem_range.mp (coe_mem n)
            conv at this =>
              arg 2
              rw [hcard]
            omega
          ⟩, by apply mem_of_subset (subset_of_ssubset ht); apply coe_mem⟩
      invFun y :=
        if h : y = x then
          ⟨#t, by apply mem_range.mpr; omega⟩
        else
          ⟨e.invFun ⟨y, by simpa [t]⟩, by
            apply mem_range.mpr
            rw [hcard]
            have := mem_range.mp (coe_mem (e.invFun ⟨y, by simpa [t]⟩))
            omega⟩
      left_inv := by
        intro n
        by_cases n = #t
        case pos hn =>
          simp [hn]
          apply Subtype.coe_eq_of_eq_mk
          simp
          symm; assumption
        case neg hn =>
          simp [hn]
          intro h
          have : x ∈ t := by rw [←h]; apply coe_mem
          have : x ∉ t := not_mem_erase x s
          contradiction
      right_inv := by
        intro y
        by_cases y = x
        case pos hy =>
          simp [hy]
          apply Subtype.coe_eq_of_eq_mk
          rw [hy]
        case neg hy =>
          simp [hy]
          intro h
          have hlt z : ↑(e.symm z) < #t := by
            apply mem_range.mp
            apply coe_mem
          have hne z : ↑(e.symm z) ≠ #t := by
            have := hlt z
            omega
          contrapose! hne
          refine Exists.intro _ h
    }

noncomputable def finset_to_range_bij (s : Finset α) :
  range #s ≃ s := Classical.choose (finset_to_range_bij' s)

end section
