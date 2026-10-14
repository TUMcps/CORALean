module

public import CORALean.ContSet.Taylm.Float.Operations.BranchAndBound

@[expose] public section

/-!
# `Taylm.optBnb`, over a floating-point scalar

CORA's `optBnb`: branch and bound over the normalized box `[-1, 1]ⁿ` plus the remainder, the ends
rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.optBnb (T : Taylm 𝕋 n) (ε : 𝕋) (fuel : ℕ) : Interval 𝕋 :=
  let b := Taylm.branchAndBound T.terms (fun _ => ⟨neg one, one⟩) ε false fuel
  ⟨addDown b.inf T.remInf, addUp b.sup T.remSup⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
