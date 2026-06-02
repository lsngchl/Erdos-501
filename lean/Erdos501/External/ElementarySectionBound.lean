import Erdos501.External.SectionBound

open Set MeasureTheory
open scoped ENNReal Topology

namespace Erdos501

namespace ElementarySectionBound

abbrev RealBasis := TopologicalSpace.countableBasis ℝ

lemma realBasis_open (I : RealBasis) : IsOpen (I : Set ℝ) :=
  TopologicalSpace.isOpen_of_mem_countableBasis I.property

lemma exists_realBasis_subset_of_isOpen {U : Set ℝ} (hU : IsOpen U) {x : ℝ}
    (hx : x ∈ U) :
    ∃ I : RealBasis, x ∈ (I : Set ℝ) ∧ (I : Set ℝ) ⊆ U := by
  rcases (TopologicalSpace.isBasis_countableBasis ℝ).exists_subset_of_mem_open hx hU with
    ⟨I, hI, hxI, hIU⟩
  exact ⟨⟨I, hI⟩, hxI, hIU⟩

/-- Horizontal section set appearing in `SectionBound`. -/
def sectionSet (A : ℝ → Set ℝ) (D : Set ℝ) (y : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ D ∧ x ∈ A y}

def basisYSet (U : ℝ → Set ℝ) (I : Set ℝ) : Set ℝ :=
  {y : ℝ | I ⊆ U y}

def envelope (U : ℝ → Set ℝ) : Set (ℝ × FullReal) :=
  ⋃ I : RealBasis, (I : Set ℝ).prod (FullReal.ofSet (basisYSet U I))

def HSet (A : ℝ → Set ℝ) (D C : Set ℝ) : Set (ℝ × FullReal) :=
  {p | p.1 ∈ D ∧ (p.2 : ℝ) ∈ C ∧ p.1 ∈ A (p.2 : ℝ)}

lemma measurableSet_fullReal_ofSet (s : Set ℝ) :
    MeasurableSet (FullReal.ofSet s) := by
  simp [FullReal.ofSet]

lemma measurableSet_basisYSet (U : ℝ → Set ℝ) (I : Set ℝ) :
    MeasurableSet (FullReal.ofSet (basisYSet U I)) :=
  measurableSet_fullReal_ofSet _

lemma measurableSet_realBasis (I : RealBasis) : MeasurableSet (I : Set ℝ) :=
  (realBasis_open I).measurableSet

lemma measurableSet_envelope (U : ℝ → Set ℝ) :
    MeasurableSet (envelope U) := by
  classical
  unfold envelope
  exact MeasurableSet.iUnion fun I =>
    (measurableSet_realBasis I).prod (measurableSet_basisYSet U I)

lemma envelope_ySection_eq {U : ℝ → Set ℝ} (hUopen : ∀ y, IsOpen (U y))
    (y : FullReal) :
    {x : ℝ | (x, y) ∈ envelope U} = U (y : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨I, hI⟩
    exact hI.2 hI.1
  · intro hxU
    rcases exists_realBasis_subset_of_isOpen (hUopen (y : ℝ)) hxU with ⟨I, hxI, hIU⟩
    exact mem_iUnion.mpr ⟨I, hxI, hIU⟩

lemma HSet_subset_envelope
    {A : ℝ → Set ℝ} {D C : Set ℝ} {U : ℝ → Set ℝ}
    (hUopen : ∀ y, IsOpen (U y))
    (hUsub : ∀ y ∈ C, sectionSet A D y ⊆ U y) :
    HSet A D C ⊆ envelope U := by
  intro p hp
  have hxU : p.1 ∈ U (p.2 : ℝ) :=
    hUsub (p.2 : ℝ) hp.2.1 ⟨hp.1, hp.2.2⟩
  have hxSec : p.1 ∈ {x : ℝ | (x, p.2) ∈ envelope U} := by
    rw [envelope_ySection_eq hUopen p.2]
    exact hxU
  exact hxSec

lemma exists_open_superset_lmeasure_le_add
    (S : Set ℝ) {δ : ℝ≥0∞}
    (hSfin : volume.toOuterMeasure S ≠ ⊤) (hδ : δ ≠ 0) :
    ∃ U : Set ℝ,
      S ⊆ U ∧ IsOpen U ∧
        volume.toOuterMeasure U ≤ volume.toOuterMeasure S + δ := by
  have hSfin' : volume S ≠ ⊤ := by
    simpa [MeasureTheory.Measure.toOuterMeasure_apply] using hSfin
  rcases Set.exists_isOpen_lt_add (μ := volume) S hSfin' hδ with
    ⟨U, hSU, hUopen, hUle⟩
  refine ⟨U, hSU, hUopen, ?_⟩
  simpa [MeasureTheory.Measure.toOuterMeasure_apply] using le_of_lt hUle

private theorem exists_approx_open_of_mem
    (A : ℝ → Set ℝ) (D C : Set ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞))
    (y : ℝ) (hy : y ∈ C) :
    ∃ U : Set ℝ,
      sectionSet A D y ⊆ U ∧ IsOpen U ∧
        volume.toOuterMeasure U ≤ volume.toOuterMeasure (sectionSet A D y) + δ := by
  exact exists_open_superset_lmeasure_le_add (sectionSet A D y)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hhor y hy)) hδ

noncomputable def approxOpen
    (A : ℝ → Set ℝ) (D C : Set ℝ) (δ : ℝ≥0∞) (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ℝ → Set ℝ := by
  classical
  exact fun y =>
    if hy : y ∈ C then
      Classical.choose (exists_approx_open_of_mem A D C hδ hhor y hy)
    else
      ∅

lemma sectionSet_subset_approxOpen
    (A : ℝ → Set ℝ) (D C : Set ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ∀ y ∈ C, sectionSet A D y ⊆ approxOpen A D C δ hδ hhor y := by
  intro y hy
  unfold approxOpen
  rw [dif_pos hy]
  exact (Classical.choose_spec (exists_approx_open_of_mem A D C hδ hhor y hy)).1

lemma isOpen_approxOpen
    (A : ℝ → Set ℝ) (D C : Set ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ∀ y, IsOpen (approxOpen A D C δ hδ hhor y) := by
  intro y
  unfold approxOpen
  by_cases hy : y ∈ C
  · rw [dif_pos hy]
    exact (Classical.choose_spec (exists_approx_open_of_mem A D C hδ hhor y hy)).2.1
  · rw [dif_neg hy]
    exact isOpen_empty

lemma measure_approxOpen_le
    (A : ℝ → Set ℝ) (D C : Set ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ∀ y ∈ C,
      volume.toOuterMeasure (approxOpen A D C δ hδ hhor y)
        ≤ volume.toOuterMeasure (sectionSet A D y) + δ := by
  intro y hy
  unfold approxOpen
  rw [dif_pos hy]
  exact (Classical.choose_spec (exists_approx_open_of_mem A D C hδ hhor y hy)).2.2

lemma approxOpen_eq_empty_of_not_mem
    (A : ℝ → Set ℝ) (D C : Set ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ∀ y, y ∉ C → approxOpen A D C δ hδ hhor y = ∅ := by
  intro y hy
  unfold approxOpen
  rw [dif_neg hy]

def fullRealIcc (n : ℕ) : Set FullReal :=
  FullReal.ofSet (Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ))

lemma iUnion_fullRealIcc :
    (⋃ n : ℕ, fullRealIcc n) = Set.univ := by
  ext y
  constructor
  · intro _hy
    trivial
  · intro _hy
    let yr : ℝ := y
    rcases exists_nat_gt |yr| with ⟨n, hn⟩
    refine mem_iUnion.mpr ⟨n, ?_⟩
    constructor
    · have hneg : -(n.succ : ℝ) ≤ -|yr| := by
        have hn' : |yr| < (n.succ : ℝ) := by
          exact lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
        linarith
      exact le_trans hneg (abs_le.mp (le_refl |yr|)).1
    · have hn' : |yr| < (n.succ : ℝ) := by
        exact lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
      exact le_of_lt (lt_of_le_of_lt (le_abs_self yr) hn')

lemma fullRealIcc_finiteMeasure (ν : FullMeasureExtension) (n : ℕ) :
    ν.μ (fullRealIcc n) < ⊤ := by
  have hEq :
      ν.μ (fullRealIcc n) =
        volume (Set.Icc (-(n.succ : ℝ)) (n.succ : ℝ)) := by
    exact ν.extends_volume _ measurableSet_Icc
  rw [hEq, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

instance fullMeasureExtension_sigmaFinite (ν : FullMeasureExtension) :
    SigmaFinite ν.μ := by
  refine ⟨⟨?_⟩⟩
  exact
    { set := fullRealIcc
      set_mem := fun _ => trivial
      finite := fullRealIcc_finiteMeasure ν
      spanning := iUnion_fullRealIcc }

lemma lintegral_vertical_sections_eq_lintegral_horizontal_sections
    (ν : FullMeasureExtension) {E : Set (ℝ × FullReal)}
    (hE : MeasurableSet E) :
    (∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ E} ∂volume)
      =
    (∫⁻ y : FullReal, volume.toOuterMeasure {x : ℝ | (x, y) ∈ E} ∂ν.μ) := by
  classical
  have hleft :
      (volume.prod ν.μ) E =
        ∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ E} ∂volume := by
    simpa using
      (MeasureTheory.Measure.prod_apply (μ := volume) (ν := ν.μ) hE)
  have hright :
      (volume.prod ν.μ) E =
        ∫⁻ y : FullReal, volume {x : ℝ | (x, y) ∈ E} ∂ν.μ := by
    simpa using
      (MeasureTheory.Measure.prod_apply_symm (μ := volume) (ν := ν.μ) hE)
  calc
    (∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ E} ∂volume)
        = ∫⁻ y : FullReal, volume {x : ℝ | (x, y) ∈ E} ∂ν.μ := hleft.symm.trans hright
    _ = ∫⁻ y : FullReal, volume.toOuterMeasure {x : ℝ | (x, y) ∈ E} ∂ν.μ := by
      simp [MeasureTheory.Measure.toOuterMeasure_apply]

lemma const_mul_outerMeasure_le_lintegral_of_le_on
    {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {D : Set ℝ} {a : ℝ≥0∞}
    (hle : ∀ x ∈ D, a ≤ f x) :
    a * volume.toOuterMeasure D ≤ ∫⁻ x, f x ∂volume := by
  classical
  let T : Set ℝ := {x : ℝ | a ≤ f x}
  have hDT : D ⊆ T := by
    intro x hx
    exact hle x hx
  have hT : MeasurableSet T := by
    exact measurableSet_le measurable_const hf
  calc
    a * volume.toOuterMeasure D ≤ a * volume.toOuterMeasure T := by
      gcongr
    _ = ∫⁻ x, T.indicator (fun _ : ℝ => a) x ∂volume := by
      rw [MeasureTheory.Measure.toOuterMeasure_apply, lintegral_indicator_const hT a]
    _ ≤ ∫⁻ x, f x ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        simpa [T] using hx
      · rw [Set.indicator_of_notMem hx]
        exact zero_le _

lemma vertical_lintegral_lower_bound
    (ν : FullMeasureExtension)
    {A : ℝ → Set ℝ} {D C : Set ℝ} {k : ℕ} {U : ℝ → Set ℝ}
    (hHsub : HSet A D C ⊆ envelope U)
    (hver : ∀ x ∈ D,
      ν.measureSet C - (k : ℝ≥0∞) ≤
        ν.measureSet {y : ℝ | y ∈ C ∧ x ∈ A y}) :
    (ν.measureSet C - (k : ℝ≥0∞)) * volume.toOuterMeasure D
      ≤ ∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ envelope U} ∂volume := by
  apply const_mul_outerMeasure_le_lintegral_of_le_on
    (measurable_measure_prodMk_left (ν := ν.μ) (measurableSet_envelope U))
  intro x hxD
  have hsub :
      FullReal.ofSet {y : ℝ | y ∈ C ∧ x ∈ A y} ⊆
        {y : FullReal | (x, y) ∈ envelope U} := by
    intro y hy
    exact hHsub ⟨hxD, hy.1, hy.2⟩
  exact le_trans (hver x hxD) (measure_mono hsub)

lemma horizontal_section_envelope_bound
    {A : ℝ → Set ℝ} {D C : Set ℝ} {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞)) :
    ∀ y : FullReal,
      volume.toOuterMeasure
          {x : ℝ | (x, y) ∈ envelope (approxOpen A D C δ hδ hhor)}
        ≤ (FullReal.ofSet C).indicator
            (fun _ : FullReal => (1 : ℝ≥0∞) + δ) y := by
  intro y
  by_cases hy : (y : ℝ) ∈ C
  · have hsec :
        {x : ℝ | (x, y) ∈ envelope (approxOpen A D C δ hδ hhor)}
          = approxOpen A D C δ hδ hhor (y : ℝ) :=
      envelope_ySection_eq (isOpen_approxOpen A D C hδ hhor) y
    rw [hsec]
    have hUle := measure_approxOpen_le A D C hδ hhor (y : ℝ) hy
    have hSle := hhor (y : ℝ) hy
    calc
      volume.toOuterMeasure (approxOpen A D C δ hδ hhor (y : ℝ))
          ≤ volume.toOuterMeasure (sectionSet A D (y : ℝ)) + δ := hUle
      _ ≤ (1 : ℝ≥0∞) + δ := by
        exact add_le_add hSle (le_refl δ)
      _ = (FullReal.ofSet C).indicator
            (fun _ : FullReal => (1 : ℝ≥0∞) + δ) y := by
        rw [Set.indicator_of_mem]
        exact hy
  · have hsec :
        {x : ℝ | (x, y) ∈ envelope (approxOpen A D C δ hδ hhor)}
          = approxOpen A D C δ hδ hhor (y : ℝ) :=
      envelope_ySection_eq (isOpen_approxOpen A D C hδ hhor) y
    rw [hsec, approxOpen_eq_empty_of_not_mem A D C hδ hhor (y : ℝ) hy]
    rw [Set.indicator_of_notMem]
    · simp
    · exact hy

lemma horizontal_lintegral_upper_bound
    (ν : FullMeasureExtension)
    {A : ℝ → Set ℝ} {D C : Set ℝ} {δ ε : ℝ≥0∞} (hδ : δ ≠ 0)
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞))
    (hδmul : δ * ν.measureSet C ≤ ε) :
    (∫⁻ y : FullReal,
      volume.toOuterMeasure
        {x : ℝ | (x, y) ∈ envelope (approxOpen A D C δ hδ hhor)} ∂ν.μ)
      ≤ ν.measureSet C + ε := by
  calc
    (∫⁻ y : FullReal,
      volume.toOuterMeasure
        {x : ℝ | (x, y) ∈ envelope (approxOpen A D C δ hδ hhor)} ∂ν.μ)
        ≤ ∫⁻ y : FullReal,
            (FullReal.ofSet C).indicator
              (fun _ : FullReal => (1 : ℝ≥0∞) + δ) y ∂ν.μ := by
          exact lintegral_mono (horizontal_section_envelope_bound hδ hhor)
    _ = ((1 : ℝ≥0∞) + δ) * ν.measureSet C := by
          rw [lintegral_indicator_const (measurableSet_fullReal_ofSet C)]
          rfl
    _ = ν.measureSet C + δ * ν.measureSet C := by
          rw [add_mul, one_mul]
    _ ≤ ν.measureSet C + ε := by
          exact add_le_add (le_refl (ν.measureSet C)) hδmul

lemma exists_delta_mul_measure_le_nnreal
    {M : ℝ≥0∞} (hM : M ≠ ⊤) {ε : NNReal} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ ≠ ⊤ ∧ δ * M ≤ (ε : ℝ≥0∞) := by
  let d : NNReal := ε / (M.toNNReal + 1)
  refine ⟨(d : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · rw [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (div_pos hε (by positivity))
  · rw [← ENNReal.coe_toNNReal hM]
    norm_cast
    dsimp [d]
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_one]
    have hden_pos : 0 < (M.toNNReal : ℝ) + 1 := by positivity
    have hMnonneg : 0 ≤ (M.toNNReal : ℝ) := by positivity
    have hεnonneg : 0 ≤ (ε : ℝ) := by positivity
    field_simp [hden_pos.ne']
    nlinarith

private theorem elementary_section_bound_aux
    (ν : FullMeasureExtension)
    {A : ℝ → Set ℝ} {D C : Set ℝ} {k : ℕ}
    (_hA : ∀ y : ℝ, volume.toOuterMeasure (A y) < (1 : ℝ≥0∞))
    (_hDfin : volume.toOuterMeasure D < ⊤)
    (hver : ∀ x ∈ D,
      ν.measureSet C - (k : ℝ≥0∞) ≤
        ν.measureSet {y : ℝ | y ∈ C ∧ x ∈ A y})
    (hhor : ∀ y ∈ C,
      volume.toOuterMeasure {x : ℝ | x ∈ D ∧ x ∈ A y} ≤ (1 : ℝ≥0∞)) :
    (ν.measureSet C - (k : ℝ≥0∞)) * volume.toOuterMeasure D ≤ ν.measureSet C := by
  classical
  by_cases hCtop : ν.measureSet C = ⊤
  · simp [hCtop]
  · have hhor' : ∀ y ∈ C,
        volume.toOuterMeasure (sectionSet A D y) ≤ (1 : ℝ≥0∞) := by
      simpa [sectionSet] using hhor
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hCfinite
    rcases exists_delta_mul_measure_le_nnreal hCtop hε with
      ⟨δ, hδ0, _hδtop, hδmul⟩
    let U : ℝ → Set ℝ := approxOpen A D C δ hδ0 hhor'
    let E : Set (ℝ × FullReal) := envelope U
    have hUopen : ∀ y, IsOpen (U y) := isOpen_approxOpen A D C hδ0 hhor'
    have hUsub : ∀ y ∈ C, sectionSet A D y ⊆ U y :=
      sectionSet_subset_approxOpen A D C hδ0 hhor'
    have hHsub : HSet A D C ⊆ E := by
      simpa [E, U] using HSet_subset_envelope (A := A) (D := D) (C := C)
        (U := U) hUopen hUsub
    have hLower :
        (ν.measureSet C - (k : ℝ≥0∞)) * volume.toOuterMeasure D
          ≤ ∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ E} ∂volume := by
      simpa [E] using vertical_lintegral_lower_bound (ν := ν) (A := A) (D := D)
        (C := C) (k := k) (U := U) hHsub hver
    have hTonelli :
        (∫⁻ x : ℝ, ν.μ {y : FullReal | (x, y) ∈ E} ∂volume)
          =
        (∫⁻ y : FullReal,
          volume.toOuterMeasure {x : ℝ | (x, y) ∈ E} ∂ν.μ) := by
      exact lintegral_vertical_sections_eq_lintegral_horizontal_sections ν
        (by simpa [E, U] using measurableSet_envelope U)
    have hUpper :
        (∫⁻ y : FullReal,
          volume.toOuterMeasure {x : ℝ | (x, y) ∈ E} ∂ν.μ)
          ≤ ν.measureSet C + (ε : ℝ≥0∞) := by
      simpa [E, U] using horizontal_lintegral_upper_bound (ν := ν) (A := A)
        (D := D) (C := C) (δ := δ) (ε := (ε : ℝ≥0∞)) hδ0 hhor' hδmul
    exact le_trans hLower (le_trans (le_of_eq hTonelli) hUpper)

theorem elementary_section_bound (ν : FullMeasureExtension) : SectionBound ν := by
  refine ⟨?_⟩
  intro A D C k hA hDfin hver hhor
  exact elementary_section_bound_aux ν hA hDfin hver hhor

end ElementarySectionBound

end Erdos501
