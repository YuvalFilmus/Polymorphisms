import Polymorphisms.SymmetricClassifyAtmost_mDefs
import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

noncomputable instance {m n : ℕ} {I : Finset (range m)} {xs : I → Finset (range n)} {fs : I → Set (Finset (range n))} :
  DecidablePred fun i ↦ xs i ∉ fs i := by
  exact Classical.decPred fun i ↦ xs i ∉ fs i

def minimal_size_set {m n w : ℕ}
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → Finset (Finset (range n))}
  {xfsb : I → Finset (range n)} (hxfsb : ∀ i : I, xfsb i ∈ fs i) :
  ∃ i₀ : I, ∃ A ∈ fs i₀, ∀ i : I, ∀ S ∈ fs i, #A ≤ #S := by
  let size (i : I) : Finset ℕ := (fs i).image card
  have size_ne (i : I) : (size i).Nonempty := by
    apply image_nonempty.mpr
    apply nonempty_of_ne_empty
    exact ne_empty_of_mem (hxfsb i)
  let min_size (i : I) : ℕ := (size i).min' (size_ne i)
  let sizes : Finset ℕ := I.attach.image min_size
  have sizes_ne : sizes.Nonempty := by
    apply image_nonempty.mpr
    apply card_pos.mp
    rw [card_attach, hI]
    omega
  have := min'_mem sizes sizes_ne
  unfold sizes at this
  rw [mem_image] at this
  obtain ⟨i₀, _, hi₀⟩ := this
  use i₀
  have := min'_mem (size i₀) (size_ne i₀)
  unfold size at this
  rw [mem_image] at this
  obtain ⟨A, memA, hA⟩ := this
  use A, memA
  intro i S hS
  calc
    #A = min_size i₀ := by
      rw [hA]
    _ ≤ min_size i := by
      rw [hi₀]
      apply min'_le
      apply mem_image.mpr
      use i
      simp
    _ ≤ #S := by
      apply min'_le
      apply mem_image.mpr
      use S

lemma exists_intersection_subset {m n : ℕ}
  {I : Finset (range m)}
  {fs : I → Finset (Finset (range n))}
  (hfs : ∀ ⦃xs : I → Finset (range n)⦄,
    (∀ j, #{i | j ∉ xs i} ≠ 1) → #{i | xs i ∉ fs i} ≠ 1)
  {xfsb : I → Finset (range n)} (hxfsb : ∀ i : I, xfsb i ∈ fs i)
  {i₀ i₁ i₂ : I} (hi₀i₁ : i₀ ≠ i₁) (hi₀i₂ : i₀ ≠ i₂) (hi₁i₂ : i₁ ≠ i₂)
  {S₀ S₁ : Finset (range n)} (hS₀ : S₀ ∈ fs i₀) (hS₁ : S₁ ∈ fs i₁) :
  ∃ S₂ ∈ fs i₂, S₂ ⊆ S₀ ∩ S₁ := by
  let xs' (i : I) := if i = i₀ then S₀ else if i = i₁ then S₁ else xfsb i
  let xs (i : I) : Finset (range n) := if i = i₂ then ({j | ∀ i ≠ i₂, j ∈ xs' i} : Finset _) else xs' i
  use xs i₂
  have sat (j : range n) : #{i | j ∉ xs i} ≠ 1 := by
    by_cases ∀ i ≠ i₂, j ∈ xs' i
    case pos h =>
      have (i : I) : j ∈ xs i := by
        by_cases i = i₂
        case neg hi =>
          simp [xs, hi]
          apply h
          exact hi
        case pos hi =>
          subst hi
          unfold xs
          simp [-Subtype.forall]
          exact h
      simp [-Subtype.forall, this]
    case neg h =>
      have hi₂ : j ∉ xs i₂ := by
        simp [-Subtype.forall, -not_forall, xs]
        exact h
      push_neg at h
      obtain ⟨i, hii₂, hi⟩ := h
      suffices 2 ≤ #(filter (fun i ↦ j ∉ xs i) univ) by omega
      have : #{i, i₂} = 2 := card_pair hii₂
      rw [←this]
      apply card_le_card
      intro i' hi'
      simp at hi'
      cases hi'
      case inl hi'i => subst hi'i; simp; simpa [xs, hii₂]
      case inr hi'i₂ => subst hi'i₂; simp; assumption
  have app := hfs sat
  constructor
  · contrapose! app
    apply card_eq_one.mpr
    use i₂
    apply eq_singleton_iff_unique_mem.mpr
    constructor
    · simp; exact app
    · intro i hi
      simp at hi
      contrapose! hi
      simp [xs, hi, xs']
      by_cases i = i₀
      case pos hi => subst hi; simpa
      case neg hi =>
      by_cases i = i₁
      case pos hi' => subst hi'; simpa [hi]
      case neg hi' =>
      simp [hi, hi']
      apply hxfsb
  · intro j hj
    simp [-Subtype.forall, xs] at hj
    simp
    constructor
    · convert hj i₀ hi₀i₂
      simp [xs']
    · convert hj i₁ hi₁i₂
      simp [xs', hi₀i₁.symm]

lemma other_ix' {α} [DecidableEq α] {I : Finset α} (hI : #I ≥ 3) (i₀ i₁ : I) :
  ∃ i₂ : I, i₀ ≠ i₂ ∧ i₁ ≠ i₂ := by
  have : (I \ {i₀.val, i₁.val}).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff]
    have : #{i₀.val, i₁.val} ≤ 2 := card_le_two
    omega
    intro i hi
    simp at hi
    cases hi
    case inl h => subst h; simp
    case inr h => subst h; simp
  have h := this.exists_mem
  choose i₂ hi₂ using h
  simp at hi₂
  obtain ⟨hmem, hi₀, hi₁⟩ := hi₂
  use ⟨i₂, hmem⟩
  constructor
  · contrapose! hi₀
    apply exists_subtype_mk_eq_iff.mp
    use hmem
    exact hi₀.symm
  · contrapose! hi₁
    apply exists_subtype_mk_eq_iff.mp
    use hmem
    exact hi₁.symm

lemma includes_min {m n : ℕ}
  {I : Finset (range m)} (hI : #I ≥ 3)
  {fs : I → Finset (Finset (range n))}
  (hfs : ∀ ⦃xs : I → Finset (range n)⦄,
    (∀ j, #{i | j ∉ xs i} ≠ 1) → #{i | xs i ∉ fs i} ≠ 1)
  {xfsb : I → Finset (range n)} (hxfsb : ∀ i : I, xfsb i ∈ fs i)
  {i₀ i₁ : I} (hi₀i₁ : i₀ ≠ i₁)
  {S₀} (hS₀mem : S₀ ∈ fs i₀) (hS₀min : ∀ i : I, ∀ S ∈ fs i, #S₀ ≤ #S)
  {S₁} (hS₁ : S₁ ∈ fs i₁) : S₀ ⊆ S₁ := by
  obtain ⟨i₂, hi₀i₂, hi₁i₂⟩ := other_ix' hI i₀ i₁
  obtain ⟨S₂, hS₂mem, hS₂⟩ := exists_intersection_subset hfs hxfsb hi₀i₁ hi₀i₂ hi₁i₂ hS₀mem hS₁
  have : S₂ ⊆ S₀ := (subset_inter_iff.mp hS₂).left
  have : S₂ = S₀ := by
    by_contra! h
    have : S₂ ⊂ S₀ := ssubset_of_subset_of_ne this h
    have : #S₂ < #S₀ := card_lt_card this
    have := hS₀min i₂ S₂ hS₂mem
    omega
  subst this
  exact (subset_inter_iff.mp hS₂).right

lemma contains_min {m n : ℕ}
  {I : Finset (range m)} (hI : #I ≥ 3)
  {fs : I → Finset (Finset (range n))}
  (hfs : ∀ ⦃xs : I → Finset (range n)⦄,
    (∀ j, #{i | j ∉ xs i} ≠ 1) → #{i | xs i ∉ fs i} ≠ 1)
  {xfsb : I → Finset (range n)} (hxfsb : ∀ i : I, xfsb i ∈ fs i)
  {i₀ i₁ : I} (hi₀i₁ : i₀ ≠ i₁)
  {S₀} (hS₀mem : S₀ ∈ fs i₀) (hS₀min : ∀ i : I, ∀ S ∈ fs i, #S₀ ≤ #S) :
  S₀ ∈ fs i₁ := by
  obtain ⟨i₂, hi₀i₂, hi₁i₂⟩ := other_ix' hI i₀ i₁
  obtain ⟨S₁, hS₁mem, hS₁⟩ := exists_intersection_subset hfs hxfsb hi₀i₂ hi₀i₁ hi₁i₂.symm hS₀mem (hxfsb i₂)
  convert hS₁mem
  by_contra! h
  replace hS₁ := (subset_inter_iff.mp hS₁).left
  have : S₁ ⊂ S₀ := ssubset_of_subset_of_ne hS₁ h.symm
  have : #S₁ < #S₀ := card_lt_card this
  have := hS₀min i₁ S₁ hS₁mem
  omega

lemma includes_all {m n : ℕ}
  {I : Finset (range m)} (hI : #I ≥ 3)
  {fs : I → Finset (Finset (range n))}
  (hfs : ∀ ⦃xs : I → Finset (range n)⦄,
    (∀ j, #{i | j ∉ xs i} ≠ 1) → #{i | xs i ∉ fs i} ≠ 1)
  {A} (hcontains : ∀ i : I, A ∈ fs i)
  (i₀ : I) {S} (hS : A ⊆ S) : S ∈ fs i₀ := by
  let xs (i : I) := if i = i₀ then S else A
  have sat (j : range n) : #{i | j ∉ xs i} ≠ 1 := by
    by_cases j ∈ A
    case pos hj =>
      have (i : I) : j ∈ xs i := by
        simp [xs]
        split
        case isTrue h =>
          subst h
          exact hS hj
        case isFalse h =>
          exact hj
      simp [this]
    case neg hj =>
      by_contra! hsingleton
      have : ({i | i ≠ i₀} : Finset I) ⊆ ({i | j ∉ xs i} : Finset I) := by
        intro i hi
        simp at hi
        simpa [xs, hi]
      have := card_le_card this
      have : #{i | i ≠ i₀} = #I - 1 := by
        have : ({i | i ≠ i₀} : Finset I) = ({i₀} : Finset I)ᶜ := by
          apply Finset.ext_iff.mpr
          intro i
          simp
        rw [this]
        simp [card_compl]
      omega
  have app := hfs sat
  contrapose! app
  apply card_eq_one.mpr
  use i₀
  apply eq_singleton_iff_unique_mem.mpr
  constructor
  · simpa [xs]
  · intro i hi
    simp at hi
    contrapose! hi
    simp [xs, hi, hcontains i]

lemma atmost_m_polymorphisms_only_if_nonconst'' {m n w : ℕ} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → Finset (Finset (range n))}
  (hfs : ∀ ⦃xs : I → Finset (range n)⦄,
    (∀ j, #{i | j ∉ xs i} ≠ 1) → #{i | xs i ∉ fs i} ≠ 1)
  {xfsb : I → Finset (range n)} (hxfsb : ∀ i : I, xfsb i ∈ fs i) :
  ∃ (J : Finset (range n)), ∀ i : I, ∀ S, S ∈ fs i ↔ J ⊆ S := by
  obtain ⟨i₀, A, hAmem, hAmin⟩ := minimal_size_set hI hxfsb
  have hI : #I ≥ 3 := by omega
  have hcontains (i : I) : A ∈ fs i := by
    by_cases i = i₀
    case pos hi =>
      subst hi
      assumption
    case neg hi =>
      push_neg at hi
      exact contains_min hI hfs hxfsb hi.symm hAmem hAmin
  have hincludes {i : I} {S} (hS : S ∈ fs i) : A ⊆ S := by
    obtain ⟨i', hii', _⟩ := other_ix' hI i i
    exact includes_min hI hfs hxfsb hii'.symm (hcontains i') hAmin hS
  use A
  intro i S
  constructor
  case mp =>
    intro h
    exact hincludes h
  case mpr =>
    intro h
    exact includes_all hI hfs hcontains i h

@[simp]
lemma boolean_if {a b : range 2} : (if a = b then b else NEG b) = a := by
    split
    case isTrue h => exact id (Eq.symm h)
    case isFalse h => exact Eq.symm (NEG_of_ne h)

lemma atmost_m_polymorphisms_only_if_nonconst' {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  {xfsb : I → range n → range 2} (hxfsb : ∀ i : I, fs i (xfsb i) = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b := by
  let fs' (i : I) : Finset (Finset (range n)) :=
    {S | fs i (fun j ↦ if j ∈ S then b else NEG b) = b}
  let xfsb' (i : I) : Finset (range n) := {j | xfsb i j = b}
  have hfs' (xs' : I → Finset (range n)) :
    (∀ j, #{i | j ∉ xs' i} ≠ 1) → #{i | xs' i ∉ fs' i} ≠ 1 := by
    intro hxs'
    let xs (i : I) (j : range n) : range 2 := if j ∈ xs' i then b else NEG b
    have (j : range n) : #{(i : I) | xs i j ≠ b} ≠ 1 := by
      convert hxs' j with i
      simp [xs, (NEG_ne b).symm]
    convert hfs this with i
    simp [fs', xs]
  have hxfsb' (i : I) : xfsb' i ∈ fs' i := by
    simp [xfsb', fs', hxfsb i]
  obtain ⟨J, hJ⟩ := atmost_m_polymorphisms_only_if_nonconst'' hw hI hfs' hxfsb'
  use J
  intro i
  replace hJ := hJ i
  funext x
  let x' : Finset (range n) := {j | x j = b}
  replace hJ := hJ x'
  simp [fs', x'] at hJ
  by_cases fs i x = b
  case pos h =>
    rw [h]; symm
    replace hJ := hJ.mp h
    simp [AND', (NEG_ne b).symm]
    intro j' rj' hj
    replace hJ := hJ hj
    simp at hJ
    exact hJ
  case neg h =>
    replace hJ : ¬ (J ⊆ filter (fun j ↦ x j = b) (range n).attach) := by tauto
    replace h := NEG_of_ne h
    rw [h]; symm
    apply NEG_of_ne
    contrapose! hJ
    intro j hj
    simp
    unfold AND' at hJ
    split at hJ
    case isTrue hJ' => exact hJ' j hj
    case isFalse hJ' => exfalso; apply NEG_ne b; exact hJ.symm

lemma atmost_m_polymorphisms_only_if_nonconst {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  (hb : ∀ i : I, ∃ x, fs i x = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b := by
  let xfsb (i : I) := (hb i).choose
  let hxfsb (i : I) : fs i (xfsb i) = b := (hb i).choose_spec
  exact atmost_m_polymorphisms_only_if_nonconst' hw hI hfs hxfsb

end NontrivialType
