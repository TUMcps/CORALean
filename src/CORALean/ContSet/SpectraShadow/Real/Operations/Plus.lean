import CORALean.Global.BlockDiag
import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.plus`

CORA's `@spectraShadow/plus`: centres add, generators concatenate, and the two
linear matrix inequalities lie along the diagonal of one, each variable acting on
its own block only. The first set's variables see a zero block in the second set's
rows, and conversely, so the inequality holds exactly when both do.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.plus (S₁ S₂ : SpectraShadow α) : SpectraShadow α where
  k := S₁.k + S₂.k
  m := S₁.m + S₂.m
  A₀ := blockDiag 0 S₁.A₀ S₂.A₀
  A := Fin.append (fun i => blockDiag 0 (S₁.A i) 0) (fun i => blockDiag 0 0 (S₂.A i))
  c := S₁.c + S₂.c
  G := Fin.append S₁.G S₂.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
