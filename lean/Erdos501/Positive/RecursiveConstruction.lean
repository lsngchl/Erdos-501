import Erdos501.Positive.KeySelection

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

/-- Remaining candidates after excluding conflicts with a finite list. -/
def CList (A : ℝ → Set ℝ) (l : List ℝ) : Set ℝ :=
  {x : ℝ | ∀ z ∈ l, x ∉ A z ∧ x ∉ B A z ∧ x ≠ z}

@[simp] theorem CList_nil (A : ℝ → Set ℝ) :
    CList A [] = Set.univ := by
  ext x
  simp [CList]

theorem mem_CList_append_singleton {A : ℝ → Set ℝ} {x a : ℝ} {l : List ℝ} :
    x ∈ CList A (l ++ [a]) ↔
      x ∈ CList A l ∧ x ∉ A a ∧ x ∉ B A a ∧ x ≠ a := by
  constructor
  · intro hx
    have hxList : x ∈ CList A l := by
      intro z hz
      exact hx z (by simp [hz])
    have hxa : x ∉ A a ∧ x ∉ B A a ∧ x ≠ a := hx a (by simp)
    exact ⟨hxList, hxa.1, hxa.2.1, hxa.2.2⟩
  · rintro ⟨hxList, hxA, hxB, hxne⟩ z hz
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · exact hxList z hz
    · have hza : z = a := by
        simpa using hz
      subst z
      exact ⟨hxA, hxB, hxne⟩

theorem CList_append_singleton_eq {A : ℝ → Set ℝ} {a : ℝ} {l : List ℝ} :
    CList A (l ++ [a]) =
      (CList A l \ B A a) \ (A a ∪ {a}) := by
  ext x
  rw [mem_CList_append_singleton]
  constructor
  · rintro ⟨hxList, hxA, hxB, hxne⟩
    refine ⟨⟨hxList, hxB⟩, ?_⟩
    intro hxUnion
    rcases hxUnion with hA | hxSingleton
    · exact hxA hA
    · exact hxne (by simpa using hxSingleton)
  · rintro ⟨⟨hxList, hxB⟩, hxNotUnion⟩
    refine ⟨hxList, ?_, hxB, ?_⟩
    · intro hxA
      exact hxNotUnion (Or.inl hxA)
    · intro hxEq
      exact hxNotUnion (Or.inr (by simp [hxEq]))

noncomputable def chooseGood
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (l : List ℝ) (hl : ν.measureSet (CList A l) = ⊤) : ℝ :=
  Classical.choose (hKey A (CList A l) hA hl)

theorem chooseGood_mem
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (l : List ℝ) (hl : ν.measureSet (CList A l) = ⊤) :
    chooseGood ν hKey A hA l hl ∈ CList A l :=
  (Classical.choose_spec (hKey A (CList A l) hA hl)).1

theorem chooseGood_keeps_top
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (l : List ℝ) (hl : ν.measureSet (CList A l) = ⊤) :
    ν.measureSet (CList A l \ B A (chooseGood ν hKey A hA l hl)) = ⊤ :=
  (Classical.choose_spec (hKey A (CList A l) hA hl)).2

theorem finite_forbidden_set
    (ν : FullMeasureExtension) {A : ℝ → Set ℝ}
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (a : ℝ) :
    ν.measureSet (A a ∪ {a}) < ⊤ :=
  ν.union_lt_top (ν.finite_of_outer_lt_one (hA a)) (by
    rw [ν.singleton a]
    norm_num)

noncomputable def goodPrefix
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) :
    (n : ℕ) → {l : List ℝ // l.length = n ∧ ν.measureSet (CList A l) = ⊤}
  | 0 => ⟨[], by simp, by simpa using ν.univ⟩
  | n + 1 =>
      let prev := goodPrefix ν hKey A hA n
      let a := chooseGood ν hKey A hA prev.1 prev.2.2
      ⟨prev.1 ++ [a], by simp [prev.2.1], by
        have hTop :
            ν.measureSet (CList A prev.1 \ B A a) = ⊤ :=
          chooseGood_keeps_top ν hKey A hA prev.1 prev.2.2
        have hFinite : ν.measureSet (A a ∪ {a}) < ⊤ :=
          finite_forbidden_set ν hA a
        have hNext :
            ν.measureSet ((CList A prev.1 \ B A a) \ (A a ∪ {a})) = ⊤ :=
          ν.measure_diff_top_of_finite hTop hFinite
        simpa [CList_append_singleton_eq, a] using hNext⟩

noncomputable def sequence
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) :
    ℕ → ℝ :=
  fun n =>
    chooseGood ν hKey A hA
      (goodPrefix ν hKey A hA n).1
      (goodPrefix ν hKey A hA n).2.2

theorem goodPrefix_succ_val
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (n : ℕ) :
    (goodPrefix ν hKey A hA (n + 1)).1 =
      (goodPrefix ν hKey A hA n).1 ++ [sequence ν hKey A hA n] := by
  rfl

theorem sequence_mem_CList
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (n : ℕ) :
    sequence ν hKey A hA n ∈ CList A (goodPrefix ν hKey A hA n).1 :=
  chooseGood_mem ν hKey A hA
    (goodPrefix ν hKey A hA n).1
    (goodPrefix ν hKey A hA n).2.2

theorem sequence_mem_goodPrefix_of_lt
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    {i n : ℕ} (hin : i < n) :
    sequence ν hKey A hA i ∈ (goodPrefix ν hKey A hA n).1 := by
  induction n with
  | zero =>
      exact False.elim (Nat.not_lt_zero i hin)
  | succ n ih =>
      rw [goodPrefix_succ_val]
      rw [List.mem_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hin with hin | rfl
      · exact Or.inl (ih hin)
      · exact Or.inr (by simp)

theorem sequence_ne_of_lt
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    {i j : ℕ} (hij : i < j) :
    sequence ν hKey A hA i ≠ sequence ν hKey A hA j := by
  have hjC := sequence_mem_CList ν hKey A hA j
  have hiMem := sequence_mem_goodPrefix_of_lt ν hKey A hA hij
  have hne : sequence ν hKey A hA j ≠ sequence ν hKey A hA i :=
    (hjC (sequence ν hKey A hA i) hiMem).2.2
  exact fun hEq => hne hEq.symm

theorem sequence_injective
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) :
    Function.Injective (sequence ν hKey A hA) := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact (sequence_ne_of_lt ν hKey A hA hlt) hij
  · exact (sequence_ne_of_lt ν hKey A hA hgt) hij.symm

theorem sequence_not_mem_A_of_lt
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    {i j : ℕ} (hij : i < j) :
    sequence ν hKey A hA i ∉ A (sequence ν hKey A hA j) := by
  have hjC := sequence_mem_CList ν hKey A hA j
  have hiMem := sequence_mem_goodPrefix_of_lt ν hKey A hA hij
  exact (hjC (sequence ν hKey A hA i) hiMem).2.1

theorem sequence_not_mem_A_of_gt
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    {i j : ℕ} (hji : j < i) :
    sequence ν hKey A hA i ∉ A (sequence ν hKey A hA j) := by
  have hiC := sequence_mem_CList ν hKey A hA i
  have hjMem := sequence_mem_goodPrefix_of_lt ν hKey A hA hji
  exact (hiC (sequence ν hKey A hA j) hjMem).1

theorem sequence_range_pairwise
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) :
    (Set.range (sequence ν hKey A hA)).Pairwise (fun x y => x ∉ A y) := by
  intro x hx y hy hxy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  have hij : i ≠ j := by
    intro h
    exact hxy (by simp [h])
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact sequence_not_mem_A_of_lt ν hKey A hA hlt
  · exact sequence_not_mem_A_of_gt ν hKey A hA hgt

theorem strongP_of_key_selection
    (ν : FullMeasureExtension) (hKey : KeySelectionPrinciple ν) :
    StrongP := by
  intro A hA
  let f : ℕ → ℝ := sequence ν hKey A hA
  refine ⟨Set.range f, ?_, ?_⟩
  · have hf : Function.Injective f := by
      simpa [f] using sequence_injective ν hKey A hA
    exact (Set.infinite_range_iff hf).mpr inferInstance
  · simpa [f] using sequence_range_pairwise ν hKey A hA

end Erdos501
