module

public import CORALean.ContSet.ConZonotope.Float.Operations.FourierMotzkinIter
public import CORALean.ContSet.ConZonotope.Float.Theorems.FourierMotzkinBoundsOuter

@[expose] public section

/-!
# The float Fourier-Motzkin iteration encloses the constrained hypercube

[1, Prop. 3] iterated, as `Real.ConZonotope.fourierMotzkinIter_outer`, for the stored floats: a
point of the unit box meeting `C x ≤ d` stays in the bounds after every pass
(`fourierMotzkinBounds_outer`), the first pass starting from the unit box, whose bounds `-1` and `1`
are exact.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `k` – number of passes
* `x` – point

## Hypotheses
* `hx` – `x` lies in the unit box
* `hC` – `x` satisfies every row `C x ≤ d`

## Conclusion
* `x` lies in the bounds after `k` passes

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       04-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.fourierMotzkinIter_outer (C : Mat 𝕋 p q) (d : Vec 𝕋 p) (k : ℕ)
    {x : Vec ℝ q} (hx : ∀ j, |x j| ≤ 1)
    (hC : ∀ i, ∑ j, toReal (C i j) * x j ≤ toReal (d i)) : -- --- CONCL ---
    x ∈ (ConZonotope.fourierMotzkinIter C d k).toSet := by -- --- PROOF ---
  -- the unit box holds `x`: its bounds read `-1` and `1`
  have h0 : x ∈ (⟨fun _ => neg one, fun _ => one⟩ : Interval (Vec 𝕋 q)).toSet := by
    intro j
    show toReal (neg one) ≤ x j ∧ x j ≤ toReal (one : 𝕋)
    rw [toReal_neg, toReal_one]
    exact abs_le.1 (hx j)
  -- each pass keeps `x`
  suffices h : ∀ k, x ∈ ((ConZonotope.fourierMotzkinBounds C d)^[k]
      (⟨fun _ => neg one, fun _ => one⟩ : Interval (Vec 𝕋 q))).toSet from h k
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ConZonotope.fourierMotzkinBounds_outer C d _ ih hC

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
