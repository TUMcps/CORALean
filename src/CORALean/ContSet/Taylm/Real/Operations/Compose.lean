module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Pow
public import CORALean.ContSet.Taylm.Real.Operations.Smul
public import CORALean.ContSet.Taylm.Real.Operations.Minus
public import CORALean.ContSet.Taylm.Real.Operations.Plus

@[expose] public section

/-!
# Composing a polynomial with a Taylor model

`Σₖ a k (T - c)ᵏ` for `k ≤ N`, plus `[-ρ, ρ]`: the shape every elementary function of CORA
takes (`exp`, `log`, `sqrt`, …), with the coefficients and the remainder bound left to the
caller. `ComposeOuter` says what `ρ` has to bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.compose (T : Taylm n) (c : ℝ) (a : ℕ → ℝ) (N : ℕ) (ρ : ℝ) : Taylm n :=
  (Taylm.sum fun k : Fin (N + 1) =>
    ((T.minus (Taylm.const n c T.maxOrder)).pow k).smul (a k)).plus ⟨[], -ρ, ρ, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
