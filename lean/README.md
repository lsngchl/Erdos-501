# Lean Formalization for Erdős Problem 501

This directory contains the Lean formalization accompanying the June 1 version
of the paper:

- `../2026-06-01_Erdos501.tex`
- `../main-v2.pdf`

The entry point is `Erdos501/Main.lean`. The main formalized theorem is the
paper's positive result under the Full Measure Extension Axiom, and the CH
counterexample from the appendix is also formalized:

```lean
Erdos501.fmea_implies_P : FMEA -> P
Erdos501.fmea_implies_StrongP : FMEA -> StrongP
Erdos501.ch_implies_not_P : CH -> ¬ P
```

Here `P` is the affirmative statement of Erdős problem #501, and `FMEA` is
formalized as the existence of a countably additive measure on all subsets of
the real line extending Lebesgue measure on measurable sets.

## Build

Install Lean through `elan`, then run:

```bash
cd lean
lake exe cache get
lake build
```

The Lean version is pinned by `lean-toolchain`, and Mathlib is pinned through
`lake-manifest.json`.

## Files

- `Erdos501/Basic.lean`: statements `P`, `StrongP`, `CH`, and basic predicates.
- `Erdos501/MeasureExtension.lean`: full measure extension formalization.
- `Erdos501/External/`: elementary section-bound proof.
- `Erdos501/Positive/`: proof of `FMEA -> P`.
- `Erdos501/Negative/`: Hechler counterexample under `CH`.
