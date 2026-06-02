import Erdos501.MeasureExtension

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

/-!
Stable section-bound interface used by the positive direction.

The June 1 proof replaces the earlier Fremlin/Kunen citation by an elementary
open-envelope argument. Downstream selection files depend on this interface.
-/

/-- Tailored section inequality used in the key-selection proof. -/
structure SectionBound (ν : FullMeasureExtension) : Prop where
  bound :
    ∀ {A : ℝ → Set ℝ} {D C : Set ℝ} {k : ℕ},
      (∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) →
      volume.toOuterMeasure D < ⊤ →
      (∀ x ∈ D,
        ν.measureSet C - (k : ℝ≥0∞) ≤
          ν.measureSet {y : ℝ | y ∈ C ∧ x ∈ A y}) →
      (∀ y ∈ C,
        volume.toOuterMeasure {x : ℝ | x ∈ D ∧ x ∈ A y} ≤ (1 : ℝ≥0∞)) →
      (ν.measureSet C - (k : ℝ≥0∞)) * volume.toOuterMeasure D ≤ ν.measureSet C

end Erdos501
