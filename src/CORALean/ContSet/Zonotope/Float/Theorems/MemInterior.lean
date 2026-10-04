import CORALean.ContSet.Zonotope.Float.Theorems.BoxSubset
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# A point strictly inside the certified box is interior to the nominal set

The open box of radius `B` around the centre lies in the nominal set (`Zonotope.box_subset`), so
a point strictly inside it is an interior point.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point strictly inside the box of radius `B` around the centre is interior. -/
theorem Zonotope.mem_interior {Z : Zonotope 𝕋 n} {H : Mat 𝕋 Z.h n} {B : 𝕋}
    (hc : Zonotope.ballCert Z.G H B one = true) (y : Vec ℝ n)
    (hy : ∀ i, |y i - toReal (Z.c i)| < toReal B) :
    y ∈ interior (nominalSet Z) := by -- --- PROOF ---
  let V : Set (Vec ℝ n) := Set.pi Set.univ fun i => Metric.ball (toReal (Z.c i)) (toReal B)
  have hV : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hVsub : V ⊆ nominalSet Z := fun y hy =>
    Zonotope.box_subset hc y fun i => by
      have := hy i (Set.mem_univ i)
      rw [Metric.mem_ball, Real.dist_eq] at this
      exact this.le
  refine interior_maximal hVsub hV fun i _ => ?_
  rw [Metric.mem_ball, Real.dist_eq]
  exact hy i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
