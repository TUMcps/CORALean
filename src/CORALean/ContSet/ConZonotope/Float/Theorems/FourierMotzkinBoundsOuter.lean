module

public import CORALean.ContSet.ConZonotope.Float.Operations.FourierMotzkinBounds
public import CORALean.ContSet.Interval.Float.Theorems.ContractHalfspaceOuter
public import CORALean.ContSet.Interval.Float.Theorems.IntersectionExact

@[expose] public section

/-!
# The float Fourier-Motzkin bounds enclose the constrained hypercube

Every point of the box `B` satisfying `C x ≤ d` lies in each row's contraction
(`Interval.contractHalfspace_outer`), hence in their intersection
(`Interval.intersection_exact`), which the fold over the rows accumulates. [1, Prop. 3] for the
stored floats (`Real.ConZonotope.fourierMotzkinBounds_outer`).

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `B` – initial bounds
* `x` – point

## Hypotheses
* `hx` – `x` lies in `B`
* `hC` – `x` satisfies every row `C x ≤ d`

## Conclusion
* `x` lies in the Fourier-Motzkin bounds

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

theorem ConZonotope.fourierMotzkinBounds_outer (C : Mat 𝕋 p q) (d : Vec 𝕋 p)
    (B : Interval (Vec 𝕋 q)) {x : Vec ℝ q} (hx : x ∈ B.toSet)
    (hC : ∀ i, ∑ j, toReal (C i j) * x j ≤ toReal (d i)) : -- --- CONCL ---
    x ∈ (ConZonotope.fourierMotzkinBounds C d B).toSet := by -- --- PROOF ---
  -- the fold keeps `x` in the running box, each row's contraction containing it
  have key : ∀ (l : List (Fin p)) (J : Interval (Vec 𝕋 q)), x ∈ J.toSet →
      x ∈ (l.foldl (fun J i => J.intersection (B.contractHalfspace (C i) (d i))) J).toSet := by
    intro l
    induction l with
    | nil => exact fun J hJ => hJ
    | cons i l ih =>
      intro J hJ
      refine ih _ ?_
      rw [Interval.intersection_exact]
      exact ⟨hJ, Interval.contractHalfspace_outer B (C i) (d i) hx (hC i)⟩
  exact key _ B hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
