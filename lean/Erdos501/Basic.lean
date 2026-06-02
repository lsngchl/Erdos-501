import Mathlib

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

/-- Erdos problem #501, affirmative form. -/
def P : Prop :=
  ∀ A : ℝ → Set ℝ,
    (∀ y : ℝ, Bornology.IsBounded (A y)) →
    (∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) →
    ∃ X : Set ℝ,
      X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)

/-- Strengthening of `P`: no boundedness hypothesis. -/
def StrongP : Prop :=
  ∀ A : ℝ → Set ℝ,
    (∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) →
    ∃ X : Set ℝ,
      X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)

theorem StrongP.implies_P : StrongP → P := by
  intro hStrong A _hBound hOuter
  exact hStrong A hOuter

/-- Independent sets for an Erdos #501 family. -/
def Independent (A : ℝ → Set ℝ) (X : Set ℝ) : Prop :=
  X.Pairwise (fun x y => x ∉ A y)

@[simp] theorem independent_iff {A : ℝ → Set ℝ} {X : Set ℝ} :
    Independent A X ↔ X.Pairwise (fun x y => x ∉ A y) := Iff.rfl

/-- Reverse section: `B A x = {y : x ∈ A y}`. -/
def B (A : ℝ → Set ℝ) (x : ℝ) : Set ℝ :=
  {y : ℝ | x ∈ A y}

@[simp] theorem mem_B {A : ℝ → Set ℝ} {x y : ℝ} :
    y ∈ B A x ↔ x ∈ A y := Iff.rfl

/-- A family witnessing failure of the affirmative statement. -/
def BadFamily (A : ℝ → Set ℝ) : Prop :=
  (∀ y : ℝ, Bornology.IsBounded (A y)) ∧
  (∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞)) ∧
  ¬ ∃ X : Set ℝ,
      X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)

/-- Existence of a family witnessing failure of the affirmative statement. -/
def HasBadFamily : Prop :=
  ∃ A : ℝ → Set ℝ, BadFamily A

theorem hasBadFamily_iff_not_P : HasBadFamily ↔ ¬ P := by
  classical
  unfold HasBadFamily BadFamily P
  constructor
  · rintro ⟨A, hBound, hOuter, hNoIndependent⟩ hP
    exact hNoIndependent (hP A hBound hOuter)
  · intro hNotP
    by_contra hNoBadFamily
    apply hNotP
    intro A hBound hOuter
    by_contra hNoIndependent
    exact hNoBadFamily ⟨A, hBound, hOuter, hNoIndependent⟩

/-- Native continuum hypothesis. -/
def CH : Prop :=
  Cardinal.mk ℝ = Cardinal.aleph 1

end Erdos501
