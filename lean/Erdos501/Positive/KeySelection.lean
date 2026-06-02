import Erdos501.External.SectionBound

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

private theorem ennreal_sub_le_of_le_add_of_le
    {a b c k : ℝ≥0∞} (h : a ≤ b + c) (hc : c ≤ k) :
    a - k ≤ b := by
  rw [tsub_le_iff_right]
  exact le_trans h (by simpa [add_comm] using add_le_add_left hc b)

private theorem threshold_lt_mul_sub
    {u m : ℝ≥0∞} {k : ℕ}
    (hu : u < ⊤) (hm : m < ⊤) (hmgt : (1 : ℝ≥0∞) < m)
    (hlarge :
      ENNReal.ofReal (((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1) < u) :
    u < (u - (k : ℝ≥0∞)) * m := by
  have hu_ne : u ≠ ⊤ := ne_of_lt hu
  have hm_ne : m ≠ ⊤ := ne_of_lt hm
  have hmRgt : 1 < m.toReal := by
    have h1_ne : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have := (ENNReal.toReal_lt_toReal h1_ne hm_ne).2 hmgt
    simpa using this
  have hden_pos : 0 < m.toReal - 1 := by linarith
  have hT_nonneg :
      0 ≤ ((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1 := by
    have hfrac_nonneg : 0 ≤ (k : ℝ) * m.toReal / (m.toReal - 1) := by positivity
    linarith
  have hlargeR :
      ((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1 < u.toReal := by
    have hof_ne :
        ENNReal.ofReal (((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have := (ENNReal.toReal_lt_toReal hof_ne hu_ne).2 hlarge
    simpa [ENNReal.toReal_ofReal hT_nonneg] using this
  have hk_lt_uR : (k : ℝ) < u.toReal := by
    have : (k : ℝ) < ((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1 := by
      have hfrac_nonneg : 0 ≤ (k : ℝ) * m.toReal / (m.toReal - 1) := by positivity
      linarith
    exact lt_trans this hlargeR
  have hcalcR : u.toReal < (u.toReal - k) * m.toReal := by
    have hmul : (k : ℝ) * m.toReal / (m.toReal - 1) < u.toReal - k := by
      linarith
    have hmul' : (k : ℝ) * m.toReal < (u.toReal - k) * (m.toReal - 1) := by
      exact (div_lt_iff₀ hden_pos).mp hmul
    nlinarith
  have hk_le_u : (k : ℝ≥0∞) ≤ u := by
    rw [← ENNReal.ofReal_toReal hu_ne]
    rw [← ENNReal.ofReal_natCast k]
    exact ENNReal.ofReal_le_ofReal hk_lt_uR.le
  have hsub_fin : u - (k : ℝ≥0∞) < ⊤ := lt_of_le_of_lt tsub_le_self hu
  have hrhs_fin : (u - (k : ℝ≥0∞)) * m < ⊤ := ENNReal.mul_lt_top hsub_fin hm
  have hrhs_ne : (u - (k : ℝ≥0∞)) * m ≠ ⊤ := ne_of_lt hrhs_fin
  have hcalc_toReal : u.toReal < ((u - (k : ℝ≥0∞)) * m).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hk_le_u hu_ne,
      ENNReal.toReal_natCast]
    exact hcalcR
  exact (ENNReal.toReal_lt_toReal hu_ne hrhs_ne).mp hcalc_toReal

/-- The selection conclusion needed for the recursive construction. -/
def KeySelectionPrinciple (ν : FullMeasureExtension) : Prop :=
  ∀ A C,
    (∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) →
    ν.measureSet C = ⊤ →
    ∃ x ∈ C, ν.measureSet (C \ B A x) = ⊤

/-- The manuscript set `D_k = {x ∈ D : ν(C \ B_x) ≤ k}`. -/
def Dk (ν : FullMeasureExtension) (A : ℝ → Set ℝ) (C D : Set ℝ) (k : ℕ) : Set ℝ :=
  {x : ℝ | x ∈ D ∧ ν.measureSet (C \ B A x) ≤ (k : ℝ≥0∞)}

private theorem Dk_vertical_estimate
    (ν : FullMeasureExtension) (A : ℝ → Set ℝ) {C CM D : Set ℝ} {k : ℕ}
    (hCM_subset_C : CM ⊆ C) {x : ℝ}
    (hxD : x ∈ Dk ν A C D k) :
    ν.measureSet CM - (k : ℝ≥0∞) ≤
      ν.measureSet {y : ℝ | y ∈ CM ∧ x ∈ A y} := by
  let S : Set ℝ := {y : ℝ | y ∈ CM ∧ x ∈ A y}
  let R : Set ℝ := CM \ B A x
  have hcover : CM ⊆ S ∪ R := by
    intro y hyCM
    by_cases hxy : x ∈ A y
    · exact Or.inl ⟨hyCM, hxy⟩
    · exact Or.inr ⟨hyCM, by simpa [B] using hxy⟩
  have hR_subset : R ⊆ C \ B A x := by
    intro y hy
    exact ⟨hCM_subset_C hy.1, hy.2⟩
  have hR_le : ν.measureSet R ≤ (k : ℝ≥0∞) :=
    le_trans (ν.mono hR_subset) hxD.2
  have hCM_le : ν.measureSet CM ≤ ν.measureSet S + ν.measureSet R := by
    exact le_trans (ν.mono hcover) (ν.measure_union_le S R)
  exact ennreal_sub_le_of_le_add_of_le hCM_le hR_le

private theorem Dk_horizontal_estimate
    (A : ℝ → Set ℝ) (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    {D CM : Set ℝ} {y : ℝ} (_hy : y ∈ CM) :
    volume.toOuterMeasure {x : ℝ | x ∈ D ∧ x ∈ A y} ≤ (1 : ℝ≥0∞) := by
  exact le_trans
    (measure_mono (by
      intro x hx
      exact hx.2))
    (le_of_lt (hA y))

theorem Dk_subset (ν : FullMeasureExtension) (A : ℝ → Set ℝ) (C D : Set ℝ) (k : ℕ) :
    Dk ν A C D k ⊆ D := by
  intro x hx
  exact hx.1

theorem Dk_mono (ν : FullMeasureExtension) (A : ℝ → Set ℝ) (C D : Set ℝ) :
    Monotone (Dk ν A C D) := by
  intro k l hkl x hx
  exact ⟨hx.1, le_trans hx.2 (by exact_mod_cast hkl)⟩

theorem iUnion_Dk_eq
    (ν : FullMeasureExtension) (A : ℝ → Set ℝ) {C D : Set ℝ}
    (hDC : D ⊆ C)
    (hContr : ∀ x ∈ C, ν.measureSet (C \ B A x) < ⊤) :
    (⋃ k : ℕ, Dk ν A C D k) = D := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨k, hk⟩
    exact hk.1
  · intro hxD
    have hfinite : ν.measureSet (C \ B A x) < ⊤ := hContr x (hDC hxD)
    rcases FullMeasureExtension.exists_nat_ge_of_lt_top hfinite with ⟨k, hk⟩
    exact mem_iUnion.mpr ⟨k, hxD, hk⟩

theorem exists_large_Dk
    (ν : FullMeasureExtension) (A : ℝ → Set ℝ) {C D : Set ℝ}
    (hDC : D ⊆ C)
    (hContr : ∀ x ∈ C, ν.measureSet (C \ B A x) < ⊤)
    (hDlarge : (1 : ℝ≥0∞) < ν.measureSet D) :
    ∃ k : ℕ, (1 : ℝ≥0∞) < ν.measureSet (Dk ν A C D k) :=
  ν.exists_measure_gt_of_iUnion (Dk ν A C D)
    (Dk_mono ν A C D)
    (iUnion_Dk_eq ν A hDC hContr)
    hDlarge

theorem exists_large_bounded_Dk
    (ν : FullMeasureExtension) (A : ℝ → Set ℝ) {C : Set ℝ}
    (hC : ν.measureSet C = ⊤)
    (hContr : ∀ x ∈ C, ν.measureSet (C \ B A x) < ⊤) :
    ∃ N k : ℕ,
      (1 : ℝ≥0∞) <
        ν.measureSet (Dk ν A C (FullMeasureExtension.trunc C N) k) ∧
      (1 : ℝ≥0∞) <
        volume.toOuterMeasure (Dk ν A C (FullMeasureExtension.trunc C N) k) ∧
      volume.toOuterMeasure (Dk ν A C (FullMeasureExtension.trunc C N) k) < ⊤ := by
  rcases ν.exists_trunc_measure_gt hC (1 : ℝ≥0∞) (by norm_num) with ⟨N, hN⟩
  have hDC : FullMeasureExtension.trunc C N ⊆ C := by
    intro x hx
    exact hx.1
  rcases exists_large_Dk ν A hDC hContr hN with ⟨k, hklarge⟩
  refine ⟨N, k, hklarge, ?_, ?_⟩
  · exact lt_of_lt_of_le hklarge
      (ν.le_outer_measureSet (Dk ν A C (FullMeasureExtension.trunc C N) k))
  · exact FullMeasureExtension.outerMeasure_lt_top_of_subset_Icc
      (by
        intro x hx
        exact (FullMeasureExtension.trunc_subset_interval C N) (Dk_subset ν A C _ k hx))

theorem key_selection
    (ν : FullMeasureExtension)
    (hSec : SectionBound ν)
    (A : ℝ → Set ℝ)
    (hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (C : Set ℝ)
    (hC : ν.measureSet C = ⊤) :
    ∃ x ∈ C, ν.measureSet (C \ B A x) = ⊤ := by
  classical
  by_contra hNo
  have hContr : ∀ x ∈ C, ν.measureSet (C \ B A x) < ⊤ := by
    intro x hxC
    have hne : ν.measureSet (C \ B A x) ≠ ⊤ := by
      intro htop
      exact hNo ⟨x, hxC, htop⟩
    exact lt_top_iff_ne_top.mpr hne
  rcases exists_large_bounded_Dk ν A hC hContr with
    ⟨N, k, _hMeasureLarge, hOuterLarge, hOuterFinite⟩
  let D : Set ℝ := Dk ν A C (FullMeasureExtension.trunc C N) k
  let m : ℝ≥0∞ := volume.toOuterMeasure D
  let threshold : ℝ≥0∞ :=
    ENNReal.ofReal (((k : ℝ) * m.toReal / (m.toReal - 1)) + k + 1)
  have hthreshold_lt_top : threshold < ⊤ := ENNReal.ofReal_lt_top
  rcases ν.exists_trunc_measure_gt hC threshold hthreshold_lt_top with ⟨M, hMlarge⟩
  let CM : Set ℝ := FullMeasureExtension.trunc C M
  have hCM_subset_C : CM ⊆ C := by
    intro x hx
    exact hx.1
  have hCMfinite : ν.measureSet CM < ⊤ :=
    ν.finite_of_outer_lt_top (FullMeasureExtension.trunc_outerMeasure_lt_top C M)
  have hstrict :
      ν.measureSet CM <
        (ν.measureSet CM - (k : ℝ≥0∞)) * volume.toOuterMeasure D := by
    exact threshold_lt_mul_sub hCMfinite hOuterFinite hOuterLarge hMlarge
  have hvertical :
      ∀ x ∈ D,
        ν.measureSet CM - (k : ℝ≥0∞) ≤
          ν.measureSet {y : ℝ | y ∈ CM ∧ x ∈ A y} := by
    intro x hx
    exact Dk_vertical_estimate ν A hCM_subset_C hx
  have hhorizontal :
      ∀ y ∈ CM,
        volume.toOuterMeasure {x : ℝ | x ∈ D ∧ x ∈ A y} ≤ (1 : ℝ≥0∞) := by
    intro y hy
    exact Dk_horizontal_estimate A hA hy
  have hbound :
      (ν.measureSet CM - (k : ℝ≥0∞)) * volume.toOuterMeasure D ≤ ν.measureSet CM :=
    hSec.bound (A := A) (D := D) (C := CM) (k := k) hA hOuterFinite hvertical hhorizontal
  exact (not_lt_of_ge hbound) hstrict

theorem keySelection_of_sectionBound
    (ν : FullMeasureExtension) (hSec : SectionBound ν) :
    KeySelectionPrinciple ν := by
  intro A C hA hC
  exact key_selection ν hSec A hA C hC

end Erdos501
