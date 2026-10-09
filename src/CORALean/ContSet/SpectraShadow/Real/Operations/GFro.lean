import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.gFro`

The Frobenius norm of the generator matrix, `norm(SpS.G, 'fro')`, which CORA's `isFullDim` compares
with `1e-8` before it solves anything (`FullDimShortcut`).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SpectraShadow.gFro (S : SpectraShadow (Vec ℝ n)) : ℝ :=
  Real.sqrt (∑ j, ∑ i, S.G j i ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
