import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Operations.BallCert
/-!
# A passed `Zonotope.ballCert` puts a box of points in the nominal set

The checked rows reach every vector within `B` of the centre with coefficients of size at most
`δ = 1` (`Zonotope.ballCert_reach`), which is the unit cube of the nominal zonotope.
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

/-- The box of radius `B` around the centre lies in the nominal set. -/
theorem Zonotope.box_subset {Z : Zonotope 𝕋 n} {H : Mat 𝕋 Z.h n} {B : 𝕋}
    (hc : Zonotope.ballCert Z.G H B one = true) (y : Vec ℝ n)
    (hy : ∀ i, |y i - toReal (Z.c i)| ≤ toReal B) : y ∈ nominalSet Z := by -- --- PROOF ---
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hc
  obtain ⟨β, hβ, hβδ⟩ := hreach (fun i => y i - toReal (Z.c i)) hy
  refine Zonotope.mem_nominalSet_iff.mpr
    ⟨β, fun j => by simpa [toReal_one] using hβδ j, fun i => ?_⟩
  have := congrFun hβ i
  simp only [Matrix.mulVec, dotProduct] at this
  have h2 : ∑ j, toReal (Z.G i j) * β j = y i - toReal (Z.c i) := this
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
