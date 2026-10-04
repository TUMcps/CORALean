import CORALean.ContSet.Taylm.Float.Operations.BranchAndBound

/-!
# `Taylm.optBnbAdv`, over a floating-point scalar

CORA's `optBnbAdv`: as `optBnb`, each sub-box's polynomial re-expanded at its midpoint first.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.optBnbAdv (T : Taylm 𝕋 n) (ε : 𝕋) (fuel : ℕ) : 𝕋 × 𝕋 :=
  let b := Taylm.branchAndBound T.terms (fun _ => (neg one, one)) ε true fuel
  (addDown b.1 T.remInf, addUp b.2 T.remSup)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
