import Polymorphisms.SymmetricClassifyAtmost_mDefs
import Polymorphisms.SymmetricClassifyDefAtmost
import Polymorphisms.SymmetricClassifyAtmost_mOnlyIfNonconst
open Finset

namespace NontrivialType

lemma atmost_m_polymorphisms_only_if'' {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1) :
  (∃ (J : Finset (range n)), ∀ i : I, fs i = AND' J b) ∨
  (∃ (K : Finset I), #K = 2 ∧ ∀ i ∈ K, fs i = CONST (NEG b)) := by
  by_cases ∃ i : I, fs i = CONST (NEG b)
  case pos h =>
    right
    obtain ⟨i, hi⟩ := h
    by_cases ∃ i' : I, i' ≠ i ∧ fs i' = CONST (NEG b)
    case pos h =>
      obtain ⟨i', hi'i, hi'⟩ := h
      use {i, i'}
      constructor
      · apply card_eq_two.mpr
        use i, i'
        constructor
        · symm; assumption
        · simp
      · intro k hk
        simp at hk
        cases hk
        case inl h => subst h; assumption
        case inr h => subst h; assumption
    case neg h =>
      exfalso
      push_neg at h
      have hb (i' : I) (hi'i : i' ≠ i) : ∃ x, fs i' x = b := by
        by_contra! h'
        apply h i' hi'i
        funext x
        simp [CONST]
        apply NEG_of_ne
        apply h'
      let xs' (i' : I) (hi'i : i' ≠ i) := (hb i' hi'i).choose
      have xs'_spec (i' : I) (hi'i : i' ≠ i) : fs i' (xs' i' hi'i) = b := by
        simp [xs']
        apply (hb i' hi'i).choose_spec
      let xs (i' : I) j := if hi'i : i' = i then
        if ∀ i' : I, (hi'i : i' ≠ i) → xs' i' hi'i j = b then b else NEG b
        else xs' i' hi'i j
      have hxs (j : range n) : #{(i : I) | xs i j ≠ b} ≠ 1 := by
        by_cases ∀ i' : I, (hi'i : i' ≠ i) → xs' i' hi'i j = b
        case pos h =>
          simp [xs, h]
        case neg h =>
          have h' : ¬ ∀ (a : ℕ) (ha : a < m) (ha' : ⟨a, mem_range.mpr ha⟩ ∈ I),
            (hi'i : ⟨⟨a, mem_range.mpr ha⟩, ha'⟩ ≠ i) →
            xs' ⟨⟨a, mem_range.mpr ha⟩, ha'⟩ hi'i j = b := by
            contrapose! h
            intro i' hi'i
            apply h i'.val.val (mem_range.mp i'.val.property)
            contrapose! hi'i
            aesop
          simp [xs, h']
          by_contra! hfilter
          replace hfilter := card_eq_one.mp hfilter
          obtain ⟨a, ha⟩ := hfilter
          push_neg at h
          obtain ⟨i', hi'i, hi'⟩ := h
          apply hi'i
          replace ha := (eq_singleton_iff_unique_mem.mp ha).right
          have : i' = a := by
            apply ha
            simpa [mem_filter, hi'i]
          rw [this]
          symm
          apply ha
          simp [mem_filter]
          push_neg
          symm
          apply NEG_ne
      apply hfs hxs
      apply card_eq_one.mpr
      use i
      simp
      apply eq_singleton_iff_unique_mem.mpr
      constructor
      · simp; push_neg; symm
        convert NEG_ne b
        rw [hi]
        simp [CONST]
      · intro i' hi'
        simp at hi'
        contrapose! hi'
        simp [xs, hi']
        apply xs'_spec
        exact hi'
  case neg h =>
    left
    push_neg at h
    apply atmost_m_polymorphisms_only_if_nonconst hw hI hfs
    intro i
    replace h := h i
    contrapose! h
    funext x
    simp [CONST]
    apply NEG_of_ne
    apply h

lemma atmost_m_polymorphisms_only_if' {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (poly : PolymorphismB P n) {I : Finset (range P.m)} (hI : #I = w+2) :
  (∃ (J : Finset (range n)), ∀ i ∈ I, poly.fs i = AND' J b) ∨
  (∃ (K : Finset I), #K = 2 ∧ ∀ i ∈ K, poly.fs i = CONST (NEG b)) := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  obtain ⟨Pm', PP'⟩ := atmost_m_def' h
  subst Pm
  have hfs (xs : I → range n → range 2) :
    (∀ j, #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | poly.fs i (xs i) ≠ b} ≠ 1 := by
    intro hxs
    let ys (i : range P.m) (j : range n) : range 2 :=
      if h : i ∈ I then
        xs ⟨i, h⟩ j
      else
        if ∀ k : I, xs k j = b then b else NEG b
    have sat j : P.P (ys · j) := by
      replace hxs := hxs j
      by_cases ∀ k : I, xs k j = b
      case pos hall =>
        simp [ys, hall]
        apply (PP' _).mpr
        simp
      case neg hall =>
        have hall' :
          ¬ ∀ (a : ℕ) (ha : a < P.m) (haI : ⟨a, mem_range.mpr ha⟩ ∈ I),
          xs ⟨⟨a, mem_range.mpr ha⟩, haI⟩ j = b := by
          contrapose! hall
          intro k
          apply hall
          apply mem_range.mp
          simp
        simp [ys, hall']
        apply (PP' _).mpr
        left
        have : I.Nonempty := by
          apply card_pos.mp
          rw [hI]
          omega
        obtain ⟨i₀, hi₀⟩ := this.exists_mem
        have : #{i | (if h : i ∈ I then xs ⟨i, h⟩ j else NEG b) = b} = #{(i : I) | xs i j = b} := by
          simp
          let i' (a : range P.m) : I :=
            if ha : a ∈ I then ⟨a, ha⟩ else ⟨i₀, hi₀⟩
          let j' (a : I) : range P.m := a.val
          apply card_nbij' i' j'
          case hi =>
            intro a ha
            simp at ha
            simp
            split at ha
            case isTrue haI =>
              simp [i', haI, ha]
            case isFalse haI =>
              exfalso
              apply NEG_ne b
              symm; exact ha
          case hj =>
            intro a ha
            simp at ha
            simpa [j']
          case left_inv =>
            intro a ha
            simp [i', j']
            simp at ha
            split
            case isTrue haI =>
              simp
            case isFalse haI =>
              exfalso
              simp [haI] at ha
              apply NEG_ne b
              symm; exact ha
          case right_inv =>
            intro a ha
            simp [i', j']
        rw [this]
        simp
        have : #{(i : I) | xs i j = b} ≤ w + 2 := by
          convert card_le_univ {(i : I) | xs i j = b}
          simp [hI]
        simp at this
        have : #{(i : I) | xs i j = b} ≠ w + 2 := by
          contrapose! hall
          have : #{(i : I) | xs i j = b} = #(univ : Finset I) := by
            simpa [hI]
          have := (card_eq_iff_eq_univ _).mp this
          have := eq_univ_iff_forall.mp this
          intro k
          have := this k
          simp at this
          exact this
        simp at this
        have : #{(i : I) | xs i j = b} ≠ w + 1 := by
          contrapose! hxs
          have : ({(i : I) | xs i j ≠ b} : Finset I) = ({(i : I) | xs i j = b} : Finset I)ᶜ := by
            simp
            refine Finset.ext_iff.mpr ?_
            intro i
            simp
          rw [this]
          simp at hxs
          simp [card_compl, hI, hxs]
        simp at this
        omega
    convert (PP _).mp (poly.app ys sat) I hI with i
    simp [ys]
  convert atmost_m_polymorphisms_only_if'' hw hI hfs with J
  constructor
  · intro h i
    apply h
    simp
  · intro h i hi
    apply h ⟨i, hi⟩

lemma atmost_m_polymorphisms_only_if {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (poly : PolymorphismB P n) :
  (∃ (J : Finset (range n)), ∀ i, poly.fs i = AND' J b) ∨
  (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, poly.fs i = CONST (NEG b)) := by
  let I : Finset (range P.m) := { i | poly.fs i = CONST (NEG b) }
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  by_cases #I > m - w - 1
  case pos hI =>
    right
    obtain ⟨I', hI', sI'⟩ := extract_subset hI
    replace sI' : #I' = m - w := by omega
    use I', sI'
    intro i hi
    have : i ∈ I := hI' hi
    have := mem_filter.mp this
    exact this.right
  case neg hI =>
    left
    simp at hI
    have : #Iᶜ > w := by
      rw [card_compl]
      simp
      omega
    obtain ⟨Ic', hIc', sIc'⟩ := extract_subset this
    have hIc' {i₀} (hi₀ : i₀ ∉ Ic') :
      ∃ J, ∀ i ∈ insert i₀ Ic', poly.fs i = AND' J b := by
      have : #(insert i₀ Ic') = w + 2 := by
        rw [card_insert_of_not_mem, sIc']
        exact hi₀
      cases atmost_m_polymorphisms_only_if' h poly this
      case inl hAND' =>
        exact hAND'
      case inr hCERT =>
        exfalso
        obtain ⟨K, sK, hK⟩ := hCERT
        obtain ⟨i₁, i₂, hi₁i₂, Kdef⟩ := card_eq_two.mp sK
        let i₃ := if i₀ = i₁ then i₂ else i₁
        have hi₃ : i₃ = i₁ ∨ i₃ = i₂ := by
          simp [i₃]
          tauto
        have hi₃i₀ : i₃.val ≠ i₀ := by
          by_cases i₀ = i₁
          case pos h =>
            simp [i₃, h]
            contrapose! hi₁i₂
            symm
            apply Subtype.coe_eq_of_eq_mk
            exact hi₁i₂
          case neg h => simp [i₃, h]; contrapose! h; symm; exact h
        have hi₃Ic : i₃.val ∉ I := by
          have := mem_insert.mp i₃.property
          simp [hi₃i₀] at this
          have := hIc' this
          apply mem_compl.mp
          exact this
        have hi₃K : i₃ ∈ K := by
          cases hi₃
          case inl h => simp [Kdef, h]
          case inr h => simp [Kdef, h]
        have hi₃CONST := hK i₃ hi₃K
        apply hi₃Ic
        apply mem_filter.mpr
        simpa
    have : Ic'ᶜ.Nonempty := by
      apply sdiff_nonempty.mpr
      by_contra! h
      have := card_le_card h
      simp [Pm, sIc'] at this
      omega
    obtain ⟨i₀, hi₀⟩ := this.exists_mem
    replace hi₀ : i₀ ∉ Ic' := by
      exact (mem_sdiff.mp hi₀).right
    obtain ⟨J, hJ⟩ := hIc' hi₀
    use J
    intro i
    by_cases i ∈ Ic'
    case pos hi =>
      apply hJ
      simp [mem_insert.mpr]
      right
      exact hi
    case neg hi =>
      obtain ⟨J', hJ'⟩ := hIc' hi
      have : Ic'.Nonempty := by
        apply card_pos.mp
        omega
      obtain ⟨i₁, hi₁⟩ := this.exists_mem
      have fsJ : poly.fs i₁ = AND' J b := by
        apply hJ
        simp [mem_insert.mpr]
        right
        exact hi₁
      have fsJ' : poly.fs i₁ = AND' J' b := by
        apply hJ'
        simp [mem_insert.mpr]
        right
        exact hi₁
      have : J = J' := by
        apply AND'_eq_AND'
        rw [←fsJ, ←fsJ']
      subst this
      apply hJ'
      simp [mem_insert]

end NontrivialType
