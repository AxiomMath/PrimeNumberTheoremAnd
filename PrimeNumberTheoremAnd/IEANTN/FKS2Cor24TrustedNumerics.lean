module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trusted numerical boundaries introduced by FKS2 Corollary 24

This file collects, in one place and with **minimal imports**, the trusted numerical
`sorry`s that the formalisation of FKS2 Corollary 24 (`corollary_24_all`) **introduces**:
twenty-two bounds on compact windows `x ∈ [eᵃ, eᵇ]`, two per Table-7 row — a small-`x`
*floor* and a large-`x` *sliver*/*band* at the threshold.  Each is a finite-range
numerical datum taken from the published computations of

> M. Cully-Hugill, D. R. Johnston, T. S. Trudgian, A. Yang (FKS2),
> *Explicit bounds for `π(x)` and related functions* (arXiv:2206.12557).

## Scope

These twenty-two are the trust that Corollary 24 adds *on top of* the existing
development.  `corollary_24_all` additionally relies on trusted numerical `sorry`s that
already live elsewhere in the repository and are **not** reproduced here:

* the Büthe bounds `Buthe.theorem_2e` / `theorem_2f` (used via `Epi_le_xpow_half`),
  backing the proved Büthe `x^{-1/2}` floor segments;
* `Table4Ext.allCells_trusted` — the ancillary Table-4 cell data, backing the numerical
  mid-range envelope.

So `#print axioms corollary_24_all` reports `sorryAx` on account of those as well as of
the facts gathered here.

## What the facts are

The eleven *floor* windows are small-`x` (`x ≲ 10⁴`): there `π(x)` is an exact prime
count and `Li(x) = ∫_2^x dt / log t` a certified quadrature, so the bound is a direct
finite check with no analytic input — the "checks directly for particularly small `x`"
step of FKS2 §5.2–§5.3.  The eleven *sliver*/*band* windows sit at the Table-7 threshold
and are of a different, **tabular** character: they lie at astronomically large `x` (from
`e^43 ≈ 5·10¹⁸` up to `e^3757.6`), far beyond any direct prime count, and rest on FKS2's
interpolation of the numerical results of Theorem 6 (the "more refined collection of
values than Table 4").  None is a zero-free region or an unproved asymptotic to be
discharged inside this development; each is a finite, paper-verified numerical datum.

## Auditing

To keep imports minimal this file does not import the main development; the FKS2
abbreviation `E_π` that appears below is written out here from Mathlib primitives only:

* `Epi x` is `E_π(x) = |π(x) − Li(x)| / (x / log x)` with
  `π(x) = Nat.primeCounting ⌊x⌋₊` and `Li(x) = ∫_2^x dt / log t`.

The Table-7 bound curves (`c · (log x)^a · x^{-1/2}`, `x^{-1/k}`) are already elementary
and appear verbatim.  `Epi` is *definitionally equal* to the root-namespace `Eπ` of the
main development (`Defs.lean`); the equality is guarded by a `rfl` `example` in
`FKS2Cor24.lean`, and the row files discharge their goals by `exact` against the lemmas
below.
-/

@[expose] public section

open MeasureTheory

namespace FKS2.Cor24Trusted

/-- `E_π(x) = |π(x) − Li(x)| / (x / log x)`, written out with Mathlib primitives only
(`π(x) = Nat.primeCounting ⌊x⌋₊`, `Li(x) = ∫_2^x dt / log t`).  Definitionally equal to
the main development's root-namespace `Eπ` (`Defs.lean`). -/
noncomputable def Epi (x : ℝ) : ℝ :=
  |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| / (x / Real.log x)

/-! ### Row 1 — curve `2·log x·x^{-1/2}` -/

/-! ### Row 2 — curve `(log x)^{3/2}·x^{-1/2}` -/

/-! ### Row 3 — curve `(1/(8π))·(log x)^2·x^{-1/2}` -/

/-! ### Row 4 — curve `(log x)^2·x^{-1/2}` -/

/-! ### Row 5 — curve `(log x)^3·x^{-1/2}` -/

/-! ### Row 6 — curve `x^{-1/3}` -/

/-! ### Row 7 — curve `x^{-1/4}` -/

/-! ### Row 8 — curve `x^{-1/5}` -/

/-! ### Row 9 — curve `x^{-1/10}` -/

/-! ### Row 10 — curve `x^{-1/50}` -/

/-! ### Row 11 — curve `x^{-1/100}` -/

end FKS2.Cor24Trusted
