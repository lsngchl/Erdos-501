import Erdos501.Basic

open Set MeasureTheory
open scoped ENNReal Cardinal

namespace Erdos501

theorem outerMeasure_eq_zero_of_countable {s : Set ℝ}
    (hs : s.Countable) : volume.toOuterMeasure s = 0 := by
  simpa using hs.measure_zero volume

theorem outerMeasure_lt_one_of_countable {s : Set ℝ}
    (hs : s.Countable) : volume.toOuterMeasure s < (1 : ℝ≥0∞) := by
  rw [outerMeasure_eq_zero_of_countable hs]
  norm_num

end Erdos501
