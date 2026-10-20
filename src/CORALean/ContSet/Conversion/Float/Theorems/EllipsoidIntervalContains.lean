module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeOfMemNominalSet
public import CORALean.Global.Float.EuclideanNorm
public import CORALean.ContSet.Conversion.Float.Operations.Basic

@[expose] public section

/-!
# An ellipsoid as a box, over a floating-point scalar

CORA's `interval(E)`, `q ± sqrt(diag(Q))`: the center give or take a proposed length per
coordinate, each end rounded away from the ellipsoid, plus what the error box already held. The
square root is checked rather than taken: `Qᵢᵢ ≤ sᵢ²` rounded down is all the certificate owes,
and then `|xᵢ - qᵢ| ≤ √Qᵢᵢ ≤ |sᵢ|` for every point of the nominal part
(`abs_sub_le_of_mem_nominalSet`). Tight only up to the certificate: over ℝ the box touches the
ellipsoid on every face, here it touches whatever `s` was worth.

## Inputs
* `E` – ellipsoid
* `s` – per-coordinate scale

## Hypotheses
* `hs` – squared scale bounds each diagonal entry

## Conclusion
* ellipsoid is contained in its interval
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the box is that reach around the center, with the error box added on
theorem Ellipsoid.interval_contains (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (E.Q i i) ≤ toReal (mulDown (s i) (s i))) : -- --- CONCL ---
    E.construct ⊆ (E.interval s).construct := by -- --- PROOF ---
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  -- the nominal point is within `|sᵢ|` of the center
  have hrow : |z i - toReal (E.q i)| ≤ toReal (absolute (s i)) := by
    refine le_trans (Ellipsoid.abs_sub_le_of_mem_nominalSet hzmem i) ?_
    rw [toReal_absolute, ← Real.sqrt_sq_eq_abs, sq]
    exact Real.sqrt_le_sqrt (max_le (mul_self_nonneg _)
      (le_trans (hs i) (mulDown_le_mul (s i) (s i))))
  have hlo : toReal (E.I_error.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (E.I_error.sup i) := (he i).2
  -- each face on its own, the two roundings going opposite ways
  constructor
  · have h1 := addDown_le_add (subDown (E.q i) (absolute (s i))) (E.I_error.inf i)
    have h2 := subDown_le_sub (E.q i) (absolute (s i))
    have h3 := neg_le_of_abs_le hrow
    show toReal (addDown (subDown (E.q i) (absolute (s i))) (E.I_error.inf i)) ≤ z i + e i
    linarith
  · have h1 := add_le_addUp (addUp (E.q i) (absolute (s i))) (E.I_error.sup i)
    have h2 := add_le_addUp (E.q i) (absolute (s i))
    have h3 := le_of_abs_le hrow
    show z i + e i ≤ toReal (addUp (addUp (E.q i) (absolute (s i))) (E.I_error.sup i))
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
