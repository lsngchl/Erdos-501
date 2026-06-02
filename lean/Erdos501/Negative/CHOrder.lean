import Erdos501.Basic

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

private abbrev AlephOneType := (Cardinal.aleph (1 : Ordinal.{0})).ord.ToType

/-- A well-order of `ℝ` with countable proper initial segments. -/
structure CHOrder where
  lt : ℝ → ℝ → Prop
  irrefl : ∀ x : ℝ, ¬ lt x x
  trans : ∀ {x y z : ℝ}, lt x y → lt y z → lt x z
  trichotomy : ∀ x y : ℝ, x = y ∨ lt x y ∨ lt y x
  wf : WellFounded lt
  initial_countable : ∀ y : ℝ, ({x : ℝ | lt x y} : Set ℝ).Countable

namespace CHOrder

theorem ne_of_lt (O : CHOrder) {x y : ℝ} (hxy : O.lt x y) : x ≠ y := by
  intro h
  subst y
  exact O.irrefl x hxy

theorem not_lt_of_lt (O : CHOrder) {x y : ℝ} (hxy : O.lt x y) : ¬ O.lt y x := by
  intro hyx
  exact O.irrefl x (O.trans hxy hyx)

theorem lt_or_gt_of_ne (O : CHOrder) {x y : ℝ} (hxy : x ≠ y) :
    O.lt x y ∨ O.lt y x := by
  rcases O.trichotomy x y with hEq | hLt | hGt
  · exact False.elim (hxy hEq)
  · exact Or.inl hLt
  · exact Or.inr hGt

end CHOrder

theorem exists_CHOrder_of_CH : CH → Nonempty CHOrder := by
  intro hCH
  have hcard : Cardinal.mk ℝ = Cardinal.mk AlephOneType := by
    rw [CH] at hCH
    rw [hCH, Cardinal.mk_ord_toType]
  rcases Cardinal.eq.mp hcard with ⟨e⟩
  refine ⟨{
    lt := fun x y : ℝ => e x < e y,
    irrefl := ?_,
    trans := ?_,
    trichotomy := ?_,
    wf := ?_,
    initial_countable := ?_
  }⟩
  · intro x
    exact lt_irrefl (e x)
  · intro x y z hxy hyz
    exact lt_trans hxy hyz
  · intro x y
    rcases lt_trichotomy (e x) (e y) with hLt | hEq | hGt
    · exact Or.inr (Or.inl hLt)
    · exact Or.inl (e.injective hEq)
    · exact Or.inr (Or.inr hGt)
  · simpa [InvImage] using InvImage.wf e (wellFounded_lt :
      WellFounded fun x y : AlephOneType => x < y)
  · intro y
    have hIio : (Set.Iio (e y)).Countable := by
      exact (Cardinal.countable_iff_lt_aleph_one (Set.Iio (e y))).2
        (Cardinal.mk_Iio_toType_ord_lt (e y))
    refine (hIio.image e.symm).mono ?_
    intro x hx
    exact ⟨e x, hx, by simp⟩

end Erdos501
