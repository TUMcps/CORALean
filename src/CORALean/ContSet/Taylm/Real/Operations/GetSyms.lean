import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.getSyms`

CORA's `@taylm/getSyms`: the polynomial part of the model, without its remainder, as a symbolic
expression in the variables, `Σ c · ∏ v ^ degs` over the terms. Here the same polynomial as a
function of the variables; `sym` itself, a MATLAB symbolic object, is not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.getSyms (T : Taylm n) (t : Vec ℝ n) : ℝ :=
  (T.terms.map fun a => a.1 * ∏ k, t k ^ a.2 k).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
