# Erdos-501

This repository contains a short note on Erdős Problem 501.

The note proves that, assuming the existence of an extension of Lebesgue measure to all subsets of the real line, every family $(A_y)_{y\in\mathbb R}$ with $m^*(A_y)<1$ admits an infinite independent set. Together with Hechler's CH counterexample, this gives a relative independence result.

## Files

- `2026-MM-DD_Erdos501.tex`: LaTeX sources.
- `main.pdf`: Uses Fremlin 543C, Kunen's theorem, to obtain the key section inequality.
- `main-v2.pdf`: Proves the needed section inequality directly by an elementary argument.
- `lean/`: Lean formalization of the main formal claims in the June 1 version; see `lean/README.md`.

## Status

Preprint draft. Comments and corrections are welcome.
