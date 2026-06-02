import Erdos501.Negative.CHOrder
import Erdos501.Negative.CountableNull

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

/-- Hechler's family associated to a `CHOrder`. -/
def HechlerFamily (O : CHOrder) : ℝ → Set ℝ :=
  fun y => {x : ℝ | O.lt x y ∧ |x| ≤ |y| + 1}

theorem hechler_subset_interval (O : CHOrder) (y : ℝ) :
    HechlerFamily O y ⊆ Set.Icc (-(|y| + 1)) (|y| + 1) := by
  intro x hx
  exact (abs_le.mp hx.2)

theorem hechler_bounded (O : CHOrder) (y : ℝ) :
    Bornology.IsBounded (HechlerFamily O y) :=
  (Metric.isBounded_Icc (-(|y| + 1)) (|y| + 1)).subset
    (hechler_subset_interval O y)

theorem hechler_countable (O : CHOrder) (y : ℝ) :
    (HechlerFamily O y).Countable :=
  (O.initial_countable y).mono (by
    intro x hx
    exact hx.1)

theorem hechler_outerMeasure_eq_zero (O : CHOrder) (y : ℝ) :
    volume.toOuterMeasure (HechlerFamily O y) = 0 :=
  outerMeasure_eq_zero_of_countable (hechler_countable O y)

theorem hechler_outerMeasure_lt_one (O : CHOrder) (y : ℝ) :
    volume.toOuterMeasure (HechlerFamily O y) < (1 : ℝ≥0∞) :=
  outerMeasure_lt_one_of_countable (hechler_countable O y)

theorem no_abs_descending_by_one (f : ℕ → ℝ)
    (h : ∀ n : ℕ, |f n| > |f (n + 1)| + 1) : False := by
  have hbound : ∀ n : ℕ, |f n| + (n : ℝ) ≤ |f 0| := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        have hstep : |f (n + 1)| + ((n + 1 : ℕ) : ℝ) < |f n| + (n : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]
          linarith [h n]
        exact le_trans (le_of_lt hstep) ih
  rcases exists_nat_gt (|f 0|) with ⟨n, hn⟩
  have hnle : (n : ℝ) ≤ |f 0| := by
    calc
      (n : ℝ) ≤ |f n| + (n : ℝ) := by
        linarith [abs_nonneg (f n)]
      _ ≤ |f 0| := hbound n
  exact (not_lt_of_ge hnle) hn

theorem abs_drop_by_one
    (O : CHOrder) {X : Set ℝ}
    (hInd : X.Pairwise (fun x y => x ∉ HechlerFamily O y))
    {f : ℕ → ℝ}
    (hfX : ∀ n : ℕ, f n ∈ X)
    (hfinc : ∀ n : ℕ, O.lt (f n) (f (n + 1))) :
    ∀ n : ℕ, |f n| > |f (n + 1)| + 1 := by
  intro n
  have hne : f n ≠ f (n + 1) := O.ne_of_lt (hfinc n)
  have hnot : f n ∉ HechlerFamily O (f (n + 1)) :=
    hInd (hfX n) (hfX (n + 1)) hne
  have hnotle : ¬ |f n| ≤ |f (n + 1)| + 1 := by
    intro hle
    exact hnot ⟨hfinc n, hle⟩
  exact lt_of_not_ge hnotle

theorem hechler_not_independent_of_strict_chain
    (O : CHOrder) {X : Set ℝ}
    (hInd : X.Pairwise (fun x y => x ∉ HechlerFamily O y))
    {f : ℕ → ℝ}
    (hfX : ∀ n : ℕ, f n ∈ X)
    (hfinc : ∀ n : ℕ, O.lt (f n) (f (n + 1))) : False :=
  no_abs_descending_by_one f (abs_drop_by_one O hInd hfX hfinc)

theorem hechler_bounded_and_outer_lt_one (O : CHOrder) :
    (∀ y : ℝ, Bornology.IsBounded (HechlerFamily O y)) ∧
      (∀ y : ℝ, volume.toOuterMeasure (HechlerFamily O y) < (1 : ℝ≥0∞)) :=
  ⟨hechler_bounded O, hechler_outerMeasure_lt_one O⟩

noncomputable def chainState (O : CHOrder) (X : Set ℝ) (hX : X.Infinite) :
    ℕ → {S : Set ℝ // S.Infinite ∧ S ⊆ X}
  | 0 => ⟨X, hX, subset_rfl⟩
  | n + 1 =>
      let prev := chainState O X hX n
      let a := O.wf.min prev.1 prev.2.1.nonempty
      ⟨prev.1 \ {a}, prev.2.1.diff (Set.finite_singleton a), by
        intro x hx
        exact prev.2.2 hx.1⟩

noncomputable def chainElem (O : CHOrder) (X : Set ℝ) (hX : X.Infinite)
    (n : ℕ) : ℝ :=
  O.wf.min (chainState O X hX n).1 (chainState O X hX n).2.1.nonempty

theorem chainElem_mem_state (O : CHOrder) (X : Set ℝ) (hX : X.Infinite)
    (n : ℕ) :
    chainElem O X hX n ∈ (chainState O X hX n).1 := by
  exact O.wf.min_mem (chainState O X hX n).1 (chainState O X hX n).2.1.nonempty

theorem chainElem_mem_set (O : CHOrder) (X : Set ℝ) (hX : X.Infinite)
    (n : ℕ) :
    chainElem O X hX n ∈ X :=
  (chainState O X hX n).2.2 (chainElem_mem_state O X hX n)

theorem chainElem_succ_mem_prev_diff
    (O : CHOrder) (X : Set ℝ) (hX : X.Infinite) (n : ℕ) :
    chainElem O X hX (n + 1) ∈
      (chainState O X hX n).1 \ {chainElem O X hX n} := by
  simpa [chainElem, chainState] using
    chainElem_mem_state O X hX (n + 1)

theorem exists_strict_chain_of_infinite
    (O : CHOrder) {X : Set ℝ} (hX : X.Infinite) :
    ∃ f : ℕ → ℝ,
      (∀ n : ℕ, f n ∈ X) ∧
      (∀ n : ℕ, O.lt (f n) (f (n + 1))) := by
  let f : ℕ → ℝ := chainElem O X hX
  refine ⟨f, ?_, ?_⟩
  · intro n
    exact chainElem_mem_set O X hX n
  · intro n
    have hmem : f (n + 1) ∈ (chainState O X hX n).1 \ {f n} := by
      simpa [f] using chainElem_succ_mem_prev_diff O X hX n
    have hnext_mem : f (n + 1) ∈ (chainState O X hX n).1 := hmem.1
    have hne : f n ≠ f (n + 1) := by
      intro hEq
      exact hmem.2 (by simp [hEq])
    have hnot_gt : ¬ O.lt (f (n + 1)) (f n) := by
      simpa [f, chainElem] using
        O.wf.not_lt_min (chainState O X hX n).1 hnext_mem
    rcases O.trichotomy (f n) (f (n + 1)) with hEq | hLt | hGt
    · exact False.elim (hne hEq)
    · exact hLt
    · exact False.elim (hnot_gt hGt)

theorem hechlerFamily_bad (O : CHOrder) : BadFamily (HechlerFamily O) := by
  refine ⟨hechler_bounded O, hechler_outerMeasure_lt_one O, ?_⟩
  rintro ⟨X, hXinf, hInd⟩
  rcases exists_strict_chain_of_infinite O hXinf with ⟨f, hfX, hfinc⟩
  exact hechler_not_independent_of_strict_chain O hInd hfX hfinc

theorem chOrder_implies_hasBadFamily (O : CHOrder) : HasBadFamily :=
  ⟨HechlerFamily O, hechlerFamily_bad O⟩

theorem chOrder_implies_not_P (O : CHOrder) : ¬ P :=
  hasBadFamily_iff_not_P.mp (chOrder_implies_hasBadFamily O)

theorem ch_implies_not_P : CH → ¬ P := by
  intro hCH
  rcases exists_CHOrder_of_CH hCH with ⟨O⟩
  exact chOrder_implies_not_P O

end Erdos501
