import Polymorphisms.SymmetricClassifyDefAtmost
open Finset

namespace NontrivialType

def AND {n} (J : Finset (range n)) (b : range 2) (x : range n → range 2) : range 2 :=
  if ∀ j ∈ J, x j = b then b else NEG b

lemma AND_def {n} {J : Finset (range n)} {b : range 2} {x : range n → range 2} :
  AND J b x = b ↔ ∀ j ∈ J, x j = b := by
  constructor
  · intro h
    intro j hj
    contrapose! h
    simp [AND]
    use j.val, mem_range.mp j.property
    constructor
    exact hj
    constructor
    exact h
    exact (NEG_ne b).symm
  · intro h
    unfold AND
    split
    rfl
    rfl

def CONST {n} (b : range 2) (_ : range n → range 2) : range 2 := b

lemma atmost_m_polymorphisms_if_AND {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (J : Finset (range n)) :
  ∃ poly : PolymorphismB P n, ∀ i, poly.fs i = AND J b := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  subst Pm
  use {
    fs i := AND J b,
    app xs sat := by
      apply (PP _).mpr
      intro I sI
      replace sat j := (PP _).mp (sat j) I sI
      by_contra! hout
      obtain ⟨i, hout⟩ := card_eq_one.mp hout
      have hi : AND J b (xs i) ≠ b := by
        have : i ∈ ({i | AND J b (xs i) ≠ b} : Finset I) := by
          rw [hout]
          simp
        have := mem_filter.mp this
        exact this.right
      simp [AND] at hi
      obtain ⟨j', hj', hjJ, hj, _⟩ := hi
      let j : range n := ⟨j', mem_range.mpr hj'⟩
      replace hjJ : j ∈ J := by simpa [j]
      replace hj : xs i j ≠ b := by simpa [j]
      apply sat j
      apply card_eq_one.mpr
      use i
      ext k
      constructor
      · intro hk
        simp
        simp at hk
        contrapose! hk
        have hk' : AND J b (xs k) = b := by
          contrapose! hk
          have : k ∈ ({i | AND J b (xs i) ≠ b} : Finset I) := by
            simpa
          rw [hout] at this
          simp at this
          exact this
        contrapose! hk'
        unfold AND
        simp
        use j.val, mem_range.mp j.property
      · intro hk
        simp
        simp at hk
        subst hk
        exact hj
  }
  intro i
  simp

lemma atmost_m_polymorphisms_if_cert {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} {fs : range P.m → (range n → range 2) → range 2}
  {I : Finset (range P.m)} (sI : #I = m - w) (hI : ∀ i ∈ I, fs i = CONST (NEG b)) :
  ∃ poly : PolymorphismB P n, poly.fs = fs := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  subst Pm
  use {
    fs := fs,
    app xs sat := by
      apply (PP _).mpr
      intro K sK
      have hint : #(K ∩ I) ≥ 2 := by
        have := card_union_add_card_inter K I
        have : #(K ∪ I) ≤ P.m := calc
          #(K ∪ I) ≤ #((range P.m).attach) := by
            apply card_le_card
            intro i hi
            apply mem_attach
          _ = P.m := by
            rw [card_attach, card_range]
        omega
      suffices #{i : K | fs i (xs i) ≠ b} ≥ #(K ∩ I) by
        omega
      simp
      let L : Finset K := {i : K | i.val ∈ I}
      have : #(K ∩ I) = #L := by
        let e : {x // x ∈ K ∩ I} ≃ {x // x ∈ L} := {
          toFun i := by
            have := mem_inter.mp i.property
            use ⟨i, ?_⟩
            simp [L]
            · exact this.right
            · exact this.left
          invFun i := by
            use ⟨i, ?_⟩
            apply mem_inter.mpr
            constructor
            · simp
            · simp
              have := i.property
              unfold L at this
              have := mem_filter.mp this
              exact this.right
            · simp
          left_inv := by
            intro i
            simp
          right_inv := by
            intro i
            simp
        }
        apply card_eq_of_equiv e
      rw [this]
      apply card_le_card
      intro i hi
      simp [L] at hi
      simp [congrFun (hI i hi) (xs i), CONST]
      exact (ReductionTo1.neg₂_dichotomy rfl).mpr rfl
  }

lemma atmost_m_polymorphisms_only_if_nonconst {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1)
  (hb : ∀ i : I, ∃ x, fs i x = b) :
  ∃ (J : Finset (range n)), ∀ i : I, fs i = AND J b := by
  sorry

lemma atmost_m_polymorphisms_only_if'' {m n w : ℕ} {b : range 2} (hw : w ≥ 1)
  {I : Finset (range m)} (hI : #I = w + 2)
  {fs : I → (range n → range 2) → range 2}
  (hfs : ∀ ⦃xs : I → range n → range 2⦄,
    (∀ (j : range n), #{(i : I) | xs i j ≠ b} ≠ 1) → #{(i : I) | fs i (xs i) ≠ b} ≠ 1) :
  (∃ (J : Finset (range n)), ∀ i : I, fs i = AND J b) ∨
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

-- TODO: Prove another version of atmost_m_def which counts the number of entries equal to b
-- use this to complete the proof
lemma atmost_m_polymorphisms_only_if' {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (poly : PolymorphismB P n) {I : Finset (range P.m)} (hI : #I = w+2) :
  (∃ (J : Finset (range n)), ∀ i ∈ I, poly.fs i = AND J b) ∨
  (∃ (K : Finset I), #K = 2 ∧ ∀ i ∈ K, poly.fs i = CONST (NEG b)) := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
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
        sorry
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
        sorry
    convert (PP _).mp (poly.app ys sat) I hI with i
    simp [ys]
  convert atmost_m_polymorphisms_only_if'' hw hI hfs with J
  constructor
  · intro h i
    apply h
    simp
  · intro h i hi
    apply h ⟨i, hi⟩

lemma AND_ne_CONST {n} (b : range 2) (J : Finset (range n)) : AND J b ≠ CONST (NEG b) := by
  by_contra! h
  have := congrFun h (fun _ ↦ b)
  simp [AND, CONST] at this
  apply NEG_ne
  assumption

lemma AND_eq_AND {n} (b : range 2) (J J' : Finset (range n)) (h : AND J b = AND J' b) :
  J = J' := by
  apply Subset.antisymm
  · let x (j : range n) := if j ∈ J' then b else NEG b
    replace h := congrFun h x
    have : AND J' b x = b := by
      apply AND_def.mpr
      intro j hj
      simp [x, hj]
    rw [this] at h
    have := AND_def.mp h
    intro j hj
    have := this j hj
    simp [x, (NEG_ne b).symm] at this
    exact this
  · let x (j : range n) := if j ∈ J then b else NEG b
    replace h := congrFun h x
    have : AND J b x = b := by
      apply AND_def.mpr
      intro j hj
      simp [x, hj]
    rw [this] at h
    have := AND_def.mp h.symm
    intro j hj
    have := this j hj
    simp [x, (NEG_ne b).symm] at this
    exact this

lemma atmost_m_polymorphisms_only_if {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (poly : PolymorphismB P n) :
  (∃ (J : Finset (range n)), ∀ i, poly.fs i = AND J b) ∨
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
    have : #(univ \ I) > w := by
      rw [card_sdiff]
      conv =>
        lhs
        arg 1
        simp [Pm]
      omega
      · intro i hi
        simp
    obtain ⟨Ic', hIc', sIc'⟩ := extract_subset this
    have hIc' {i₀} (hi₀ : i₀ ∉ Ic') :
      ∃ J, ∀ i ∈ insert i₀ Ic', poly.fs i = AND J b := by
      have : #(insert i₀ Ic') = w + 2 := by
        rw [card_insert_of_not_mem, sIc']
        exact hi₀
      cases atmost_m_polymorphisms_only_if' h poly this
      case inl hAND =>
        exact hAND
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
    have : (univ \ Ic').Nonempty := by
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
      have fsJ : poly.fs i₁ = AND J b := by
        apply hJ
        simp [mem_insert.mpr]
        right
        exact hi₁
      have fsJ' : poly.fs i₁ = AND J' b := by
        apply hJ'
        simp [mem_insert.mpr]
        right
        exact hi₁
      have : J = J' := by
        apply AND_eq_AND
        rw [←fsJ, ←fsJ']
      subst this
      apply hJ'
      simp [mem_insert]

lemma atmost_m_polymorphisms {P m w b hm hw} (h : P = P_of_S (atmost_m m w b hm hw).denotation)
  {n} (fs : range P.m → (range n → range 2) → range 2) :
  (∃ poly : PolymorphismB P n, poly.fs = fs) ↔
  (∃ (J : Finset (range n)), ∀ i, fs i = AND J b) ∨
  (∃ (I : Finset (range P.m)), #I = m - w ∧ ∀ i ∈ I, fs i = CONST (NEG b))
  := by
  obtain ⟨Pm, PP⟩ := atmost_m_def h
  symm at Pm
  subst Pm
  constructor
  case mp =>
    rintro ⟨poly, hpoly⟩
    convert atmost_m_polymorphisms_only_if h poly
    repeat exact hpoly.symm
  case mpr =>
    rintro h
    cases h
    case inl h =>
      obtain ⟨J, hJ⟩ := h
      obtain ⟨poly, hpoly⟩ := atmost_m_polymorphisms_if_AND h J
      use poly
      funext i
      rw [hJ i, hpoly i]
    case inr h =>
      obtain ⟨I, sI, hI⟩ := h
      apply atmost_m_polymorphisms_if_cert h sI hI

end NontrivialType
