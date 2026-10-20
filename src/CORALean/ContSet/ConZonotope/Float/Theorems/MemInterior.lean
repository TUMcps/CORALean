module

public import CORALean.ContSet.ConZonotope.Float.Theorems.BoxSubset
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# A point strictly inside the certified box is interior to the nominal set

The open box of radius `B` around `c + G β₀` lies in the nominal set (`ConZonotope.box_subset`).

## Inputs
* `cZ` – float constrained zonotope
* `H` – right inverse of the generator matrix
* `β₀` – coefficient point
* `δ` – ball radius in coefficient space
* `B` – box radius around the center
* `y` – point of the open box

## Hypotheses
* `hc` – the interior certificate passes
* `hy` – the point is strictly within the box radius

## Conclusion
* the point is interior to the nominal set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_interior {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cZ.h n}
    {β₀ : Vec 𝕋 cZ.h} {δ B : 𝕋} (hc : cZ.interiorCert H β₀ δ B = true) (y : Vec ℝ n)
    (hy : ∀ i, |y i - (toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j))| < toReal B)
    : -- --- CONCL ---
    y ∈ interior (nominalSet cZ) := by -- --- PROOF ---
  let V : Set (Vec ℝ n) := Set.pi Set.univ fun i =>
    Metric.ball (toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)) (toReal B)
  have hV : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hVsub : V ⊆ nominalSet cZ := fun y hy =>
    ConZonotope.box_subset hc y fun i => by
      have := hy i (Set.mem_univ i)
      rw [Metric.mem_ball, Real.dist_eq] at this
      exact this.le
  refine interior_maximal hVsub hV fun i _ => ?_
  rw [Metric.mem_ball, Real.dist_eq]
  exact hy i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
