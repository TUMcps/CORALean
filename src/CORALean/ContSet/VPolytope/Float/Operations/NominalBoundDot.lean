module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.InflatedContSet.Operations.Bound

@[expose] public section

/-!
# `VPolytope.nominalBoundDot`

A general direction, at the price the coordinate ones avoid: a rounded dot
product per vertex, then the largest of them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A general direction, at the price the coordinate ones avoid: a rounded dot
product per vertex, then the largest of them. -/
def VPolytope.nominalBoundDot (P : VPolytope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (nominalSet P) c where
  val := maximumOver fun l => dotUp a (P.V l)
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le c
      (fun l => by
        rw [hc]
        exact le_trans (le_dotUp a (P.V l))
          (le_maximumOver (fun l => dotUp a (P.V l)) l)) hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
