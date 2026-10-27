module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.absorbRounding`

The error box moved into the shape matrix. The box lies in the ball of squared radius `ρ² = Σ
max(|inf|, |sup|)²`, rounded up, and the sum of two ellipsoids lies in the ellipsoid of shape `(1 +
1/β) Q₁ + (1 + β) Q₂` for every `β > 0` [1, Eq. 11], the family CORA's `ellipsoid/plus` in mode
`'outer:halder'` computes. Here `β` is the trace-optimal one [1, Sec. II-B], `√(tr Q / tr(ρ² I))`,
in floats; any positive value is sound, so a `β` not certified positive falls back to `1`. The shape
is stored rounded upward by `Ellipsoid.inflate`, the center kept. A box with `ρ²` certified `≤ 0` is
dropped; a shape `isPsd` does not certify returns the ellipsoid unchanged. `k` is the Newton steps.

## Inputs
* `k` – Newton steps for the root
* `E` – ellipsoid

## Output
* ellipsoid whose shape absorbs the error box of `E`

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid with its error box in its shape: `(1 + 1/β) Q + (1 + β) ρ² I` rounded upward,
`ρ²` bounding the box's squared Euclidean norm, and the origin as its box. -/
def Ellipsoid.absorbRounding (k : ℕ) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  -- the squared radius of a ball holding the box
  let ρ2 := sqSumUp E.I_error.normMag
  if Ellipsoid.isPsd E.Q = true then
    if le ρ2 zero = true then { E with I_error := Interval.origin n }
    else
      -- the trace-optimal parameter, `1` where it is not certified positive
      let β₀ := sqrtUp k (divUp (sumUp fun i => E.Q i i) (mulDown (nsmulUp n one) ρ2))
      let β := if ltStrict zero β₀ = true then β₀ else one
      -- the weights `1 + 1/β` and `1 + β`, rounded up
      let a := addUp one (divUp one β)
      let c := addUp one β
      { Q := Ellipsoid.inflate (Interval.matPlus (Interval.smul a a (Interval.point E.Q))
          ⟨diagonalBlock fun _ => mulDown c ρ2, diagonalBlock fun _ => mulUp c ρ2⟩)
        q := E.q
        I_error := Interval.origin n }
  else E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
