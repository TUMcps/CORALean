import CORALean.ContSet.Taylm.Real.Operations.Compose
import CORALean.ContSet.Taylm.Real.Operations.Reach
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Taylor expansion of a function at a Taylor model

`g` expanded at `c` to the model's order, `Σₖ g⁽ᵏ⁾(c)/k! (T - c)ᵏ`, and the Lagrange
remainder bounded by `D · reach^(N+1) / (N+1)!` for a `D` bounding `|g⁽ᴺ⁺¹⁾|` between `c`
and the model's range. CORA writes each elementary function out by hand in this
shape; here `exp`, `log` and `sqrt` are this definition at their own `g` and `D`. The
remainder is the magnitude form, symmetric about zero, where CORA evaluates the signed
Lagrange term in interval arithmetic: sound either way, coarser here by up to a factor two.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.taylor (T : Taylm n) (g : ℝ → ℝ) (c D : ℝ) : Taylm n :=
  T.compose c (fun k => iteratedDeriv k g c / (k.factorial : ℝ)) T.maxOrder
    (D * T.reach c ^ (T.maxOrder + 1) / ((T.maxOrder + 1).factorial : ℝ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
