module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalSubsetNominalEllipsoid

@[expose] public section

/-!
# A box as an ellipsoid, over a floating-point scalar

The smallest ellipsoid containing a box is `√n` times the inscribed one, so this is a place the
layer meets a square root, answered as elsewhere: the caller proposes `σ` and `n ≤ σ·σ` is checked,
so the classical `√n` is the tightest admissible value rather than a required one. Directly rather
than through the zonotope: a box's generators are already `diag(radiusFrom)`. The generators round
*up*, which lets the error box stay empty: a coordinate's coefficient is `(xᵢ - cᵢ)/gᵢ`, which an
upward-rounded `gᵢ` only makes smaller, so the enclosure is exact in the arithmetic, not merely paid
for. Rounding down would have cost a box.

## Inputs
* `I` – interval
* `σ` – scaling factor

## Hypotheses
* `hσ` – scaling factor positive
* `hn` – squared scaling factor at least dimension

## Conclusion
* interval is contained in its ellipsoid
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ellipsoid_contains (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) :
    I.construct ⊆ (I.ellipsoid σ).construct := fun x hx =>
  ⟨x, I.subset_nominal_ellipsoid σ hσ hn hx, 0, fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩, by show x + 0 = x; rw [add_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
