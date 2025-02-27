import Mathlib.Tactic

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

noncomputable def extend_partial_injection {f : X → X} {P : X → Bool}
  (hf : ∀ x y, f x = f y → P x → P y → x = y) : Equiv.Perm X := by
  let dom : Finset X := { x | P x }
  let cod := image f dom

  let f' (x : dom) : X := f x
  let cod' := image f' univ
  have h_inj_dom : Function.Injective f' := by
    intro x y h
    have := hf x y h (mem_filter.mp x.property).2 (mem_filter.mp y.property).2
    apply Subtype.coe_eq_of_eq_mk
    assumption

  have h_cod' : cod = cod' := by
    aesop

  have h_card_dom' : dom.card = cod'.card := by
      rw [card_image_of_injective univ h_inj_dom, card_univ, Fintype.card_coe]

  have h_card_dom : dom.card = cod.card := by
    rw [h_cod']
    exact h_card_dom'

  let rest_dom := domᶜ
  let rest_cod := codᶜ

  have h_card_rest_dom : rest_dom.card = rest_cod.card := by
    calc
      rest_dom.card = (Finset.univ.card - dom.card) := by rw [card_compl]; congr
      _ = (Finset.univ.card - cod.card) := by rw [h_card_dom]
      _ = rest_cod.card := by rw [Finset.card_compl]; congr

  let rest_bij := equivOfCardEq h_card_rest_dom

  let extended_f (x : X) : X :=
    if h : x ∈ dom then
      f x
    else
      rest_bij ⟨x, by simpa [rest_dom]⟩

  have h_inj : Function.Injective extended_f := by
    intro x y h
    by_cases x ∈ dom
    case pos hx =>
      by_cases y ∈ dom
      case pos hy =>
        simp [extended_f, hx, hy] at h
        exact hf x y h (mem_filter.mp hx).2 (mem_filter.mp hy).2
      case neg hy =>
        have hx' : extended_f x ∈ cod := by
          simp [extended_f, hx, cod]
          use x
        have hy' : extended_f y ∈ codᶜ := by
          simp [extended_f, hy]
        rw [←h, mem_compl] at hy'
        contradiction
    case neg hx =>
      by_cases y ∈ dom
      case pos hy =>
        have hx' : extended_f x ∈ codᶜ := by
          simp [extended_f, hx, cod]
        have hy' : extended_f y ∈ cod := by
          simp [extended_f, hy, cod]
          use y
        rw [h, mem_compl] at hx'
        contradiction
      case neg hy =>
        simp [extended_f, hx, hy] at h
        have := Equiv.injective rest_bij (Subtype.coe_eq_of_eq_mk h)
        apply Subtype.eq_iff.mp this

  have h_perm : Function.Bijective extended_f := by
    apply Function.Injective.bijective_of_nat_card_le h_inj
    rfl

  exact Equiv.ofBijective extended_f h_perm

def extend_partial_injection_extension {f : X → X} {P : X → Bool}
  (hf : ∀ x y, f x = f y → P x → P y → x = y) {x : X} (hx : P x) :
  extend_partial_injection hf x = f x := by
  simp [extend_partial_injection, hx]

-- sample applications

noncomputable def perm_2_to_2 {x₁ x₂ y₁ y₂ : X} (hx' : x₁ ≠ x₂) (hy' : y₁ ≠ y₂) : Equiv.Perm X := by
  let f (x : X) : X :=
    if x = x₁ then y₁ else y₂

  let P (x : X) : Bool := x = x₁ ∨ x = x₂

  have h_inj (x y : X) (hf : f x = f y) (Px : P x) (Py : P y) : x = y := by
    symm at hx'
    simp [P] at Px Py
    cases Px
    case inl hx =>
      cases Py
      case inl hy => rw [hx, hy]
      case inr hy =>
        rw [hx, hy] at hf
        simp [f, hx'] at hf
        contradiction
    case inr hx =>
      cases Py
      case inr hy => rw [hx, hy]
      case inl hy =>
        rw [hx, hy] at hf
        simp [f, hx'] at hf
        symm at hy'
        contradiction

  exact extend_partial_injection h_inj

lemma perm_2_to_2_spec {x₁ x₂ y₁ y₂ : X} (hx' : x₁ ≠ x₂) (hy' : y₁ ≠ y₂) :
  (perm_2_to_2 hx' hy' x₁ = y₁) ∧ (perm_2_to_2 hx' hy' x₂ = y₂) := by
  simp [perm_2_to_2, extend_partial_injection]
  intro h; symm at h; contradiction
