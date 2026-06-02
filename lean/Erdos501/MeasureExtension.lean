import Erdos501.Basic

open Set MeasureTheory Filter
open scoped ENNReal Cardinal Topology

namespace Erdos501

/-- A type alias for real numbers equipped with the full sigma-algebra. -/
def FullReal := ℝ

namespace FullReal

instance : MeasurableSpace FullReal := ⊤

/-- View a real set as a set of `FullReal`. -/
def ofSet (s : Set ℝ) : Set FullReal :=
  {x : FullReal | (x : ℝ) ∈ s}

@[simp] theorem mem_ofSet {s : Set ℝ} {x : FullReal} :
    x ∈ ofSet s ↔ (x : ℝ) ∈ s := Iff.rfl

end FullReal

/-- Native representation of a full extension of Lebesgue measure to all real sets. -/
structure FullMeasureExtension where
  μ : MeasureTheory.Measure FullReal
  extends_volume :
    ∀ s : Set ℝ, MeasurableSet s → μ (FullReal.ofSet s) = volume s

/-- The Full Measure Extension Axiom, represented natively. -/
def FMEA : Prop :=
  Nonempty FullMeasureExtension

namespace FullMeasureExtension

/-- Apply a full measure extension to a real set. -/
noncomputable def measureSet (ν : FullMeasureExtension) (s : Set ℝ) : ℝ≥0∞ :=
  ν.μ (FullReal.ofSet s)

@[simp] theorem measure_empty (ν : FullMeasureExtension) :
    ν.measureSet ∅ = 0 := by
  have h : FullReal.ofSet ∅ = (∅ : Set FullReal) := by
    ext x
    constructor
    · intro hx
      cases hx
    · intro hx
      cases hx
  simp [measureSet, h]

theorem mono (ν : FullMeasureExtension) {s t : Set ℝ} (h : s ⊆ t) :
    ν.measureSet s ≤ ν.measureSet t := by
  exact measure_mono (by
    intro x hx
    exact h hx)

theorem le_outer_measureSet (ν : FullMeasureExtension) (s : Set ℝ) :
    ν.measureSet s ≤ volume.toOuterMeasure s := by
  rcases MeasureTheory.exists_measurable_superset volume s with
    ⟨t, hst, ht_meas, ht_eq⟩
  calc
    ν.measureSet s ≤ ν.measureSet t := ν.mono hst
    _ = volume t := ν.extends_volume t ht_meas
    _ = volume s := ht_eq
    _ = volume.toOuterMeasure s := by
      rw [MeasureTheory.Measure.toOuterMeasure_apply]

theorem singleton (ν : FullMeasureExtension) (x : ℝ) :
    ν.measureSet ({x} : Set ℝ) = 0 := by
  calc
    ν.measureSet ({x} : Set ℝ) = volume ({x} : Set ℝ) := by
      exact ν.extends_volume ({x} : Set ℝ) (MeasurableSet.singleton x)
    _ = 0 := by simp

theorem univ (ν : FullMeasureExtension) :
    ν.measureSet Set.univ = ⊤ := by
  calc
    ν.measureSet Set.univ = volume (Set.univ : Set ℝ) := by
      exact ν.extends_volume Set.univ MeasurableSet.univ
    _ = ⊤ := by simp

theorem finite_of_outer_lt_top (ν : FullMeasureExtension) {s : Set ℝ}
    (hs : volume.toOuterMeasure s < ⊤) :
    ν.measureSet s < ⊤ :=
  lt_of_le_of_lt (ν.le_outer_measureSet s) hs

theorem finite_of_outer_lt_one (ν : FullMeasureExtension) {s : Set ℝ}
    (hs : volume.toOuterMeasure s < (1 : ℝ≥0∞)) :
    ν.measureSet s < ⊤ :=
  ν.finite_of_outer_lt_top (lt_trans hs (by norm_num))

theorem measure_union_le (ν : FullMeasureExtension) (s t : Set ℝ) :
    ν.measureSet (s ∪ t) ≤ ν.measureSet s + ν.measureSet t := by
  simpa [measureSet, FullReal.ofSet, Set.setOf_or] using
    (MeasureTheory.measure_union_le (μ := ν.μ) (FullReal.ofSet s) (FullReal.ofSet t))

theorem union_lt_top (ν : FullMeasureExtension) {s t : Set ℝ}
    (hs : ν.measureSet s < ⊤) (ht : ν.measureSet t < ⊤) :
    ν.measureSet (s ∪ t) < ⊤ := by
  calc
    ν.measureSet (s ∪ t) ≤ ν.measureSet s + ν.measureSet t := ν.measure_union_le s t
    _ < ⊤ := by
      rw [ENNReal.add_lt_top]
      exact ⟨hs, ht⟩

theorem measure_diff_top_of_finite (ν : FullMeasureExtension) {T S : Set ℝ}
    (hT : ν.measureSet T = ⊤) (hS : ν.measureSet S < ⊤) :
    ν.measureSet (T \ S) = ⊤ := by
  by_contra hne
  have hdiff : ν.measureSet (T \ S) < ⊤ := lt_top_iff_ne_top.mpr hne
  have hUnion : ν.measureSet ((T \ S) ∪ S) < ⊤ := ν.union_lt_top hdiff hS
  have hsub : T ⊆ (T \ S) ∪ S := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · exact Or.inl ⟨hx, hxS⟩
  have hle : ⊤ ≤ ν.measureSet ((T \ S) ∪ S) := by
    simpa [hT] using ν.mono hsub
  exact (not_lt_of_ge (le_refl (⊤ : ℝ≥0∞))) (lt_of_le_of_lt hle hUnion)

/-- Symmetric bounded truncation of a real set. -/
def trunc (C : Set ℝ) (N : ℕ) : Set ℝ :=
  C ∩ Set.Icc (-(N : ℝ)) (N : ℝ)

theorem trunc_subset_interval (C : Set ℝ) (N : ℕ) :
    trunc C N ⊆ Set.Icc (-(N : ℝ)) (N : ℝ) := by
  intro x hx
  exact hx.2

theorem outerMeasure_Icc_lt_top (N : ℕ) :
    volume.toOuterMeasure (Set.Icc (-(N : ℝ)) (N : ℝ)) < ⊤ := by
  rw [MeasureTheory.Measure.toOuterMeasure_apply, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem outerMeasure_lt_top_of_subset_Icc {D : Set ℝ} {N : ℕ}
    (hD : D ⊆ Set.Icc (-(N : ℝ)) (N : ℝ)) :
    volume.toOuterMeasure D < ⊤ :=
  lt_of_le_of_lt (measure_mono hD) (outerMeasure_Icc_lt_top N)

theorem trunc_outerMeasure_lt_top (C : Set ℝ) (N : ℕ) :
    volume.toOuterMeasure (trunc C N) < ⊤ :=
  outerMeasure_lt_top_of_subset_Icc (trunc_subset_interval C N)

theorem exists_trunc_measure_gt
    (ν : FullMeasureExtension) {C : Set ℝ}
    (hC : ν.measureSet C = ⊤) (a : ℝ≥0∞) (ha : a < ⊤) :
    ∃ N : ℕ, a < ν.measureSet (trunc C N) := by
  let S : ℕ → Set FullReal :=
    fun N => FullReal.ofSet (trunc C N)
  have hmono : Monotone S := by
    intro m n hmn x hx
    rcases hx with ⟨hxC, hxI⟩
    exact ⟨hxC, by
      constructor
      · have hmle : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith [hxI.1]
      · have hmle : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith [hxI.2]⟩
  have hUnion : (⋃ N, S N) = FullReal.ofSet C := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨N, hN⟩
      exact hN.1
    · intro hxC
      let xr : ℝ := x
      rcases exists_nat_gt |xr| with ⟨N, hN⟩
      refine mem_iUnion.mpr ⟨N, hxC, ?_⟩
      constructor
      · have hxneg : -(N : ℝ) ≤ - |xr| := by
          linarith
        exact le_trans hxneg (abs_le.mp (le_refl |xr|)).1
      · exact le_of_lt (lt_of_le_of_lt (le_abs_self xr) hN)
  have htendstoS : Tendsto (fun N => ν.μ (S N)) atTop (𝓝 ⊤) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν.μ) hmono
    have h' :
        Tendsto (fun N => ν.μ (S N)) atTop (𝓝 (ν.μ (⋃ N, S N))) := by
      simpa [Function.comp_def] using h
    have htop : ν.μ (⋃ N, S N) = ⊤ := by
      simpa [hUnion, FullMeasureExtension.measureSet] using hC
    simpa [htop] using h'
  have hev : ∀ᶠ N in atTop, a < ν.μ (S N) :=
    htendstoS.eventually (Ioi_mem_nhds ha)
  rcases eventually_atTop.mp hev with ⟨N, hN⟩
  exact ⟨N, by simpa [S, FullMeasureExtension.measureSet, trunc] using hN N le_rfl⟩

theorem exists_measure_gt_of_iUnion
    (ν : FullMeasureExtension) (S : ℕ → Set ℝ) {D : Set ℝ}
    (hmono : Monotone S) (hUnion : (⋃ n, S n) = D)
    {a : ℝ≥0∞} (ha : a < ν.measureSet D) :
    ∃ n : ℕ, a < ν.measureSet (S n) := by
  let T : ℕ → Set FullReal := fun n => FullReal.ofSet (S n)
  have hmonoT : Monotone T := by
    intro m n hmn x hx
    exact hmono hmn hx
  have hUnionT : (⋃ n, T n) = FullReal.ofSet D := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hn⟩
      exact hUnion ▸ mem_iUnion.mpr ⟨n, hn⟩
    · intro hx
      have hx' : (x : ℝ) ∈ ⋃ n, S n := hUnion.symm ▸ hx
      rcases mem_iUnion.mp hx' with ⟨n, hn⟩
      exact mem_iUnion.mpr ⟨n, hn⟩
  have htendstoS : Tendsto (fun n => ν.μ (T n)) atTop (𝓝 (ν.measureSet D)) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν.μ) hmonoT
    have h' :
        Tendsto (fun n => ν.μ (T n)) atTop (𝓝 (ν.μ (⋃ n, T n))) := by
      simpa [Function.comp_def] using h
    simpa [FullMeasureExtension.measureSet, hUnionT] using h'
  have hev : ∀ᶠ n in atTop, a < ν.μ (T n) :=
    htendstoS.eventually (Ioi_mem_nhds ha)
  rcases eventually_atTop.mp hev with ⟨n, hn⟩
  exact ⟨n, by simpa [T, FullMeasureExtension.measureSet] using hn n le_rfl⟩

theorem exists_nat_ge_of_lt_top {x : ℝ≥0∞} (hx : x < ⊤) :
    ∃ k : ℕ, x ≤ (k : ℝ≥0∞) := by
  rcases ENNReal.exists_nat_gt (ne_of_lt hx) with ⟨k, hk⟩
  exact ⟨k, le_of_lt hk⟩

end FullMeasureExtension

end Erdos501
