import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.translate`

A shadow shifted by a vector: only the centre moves, the inequality is untouched. CORA's
`SpS - c` and `SpS + c` for a numeric `c` (`@spectraShadow/plus.m` with a point), as the
shift of the set by `v` is the centre `c + v`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.translate (S : SpectraShadow α) (v : α) : SpectraShadow α :=
  { S with c := S.c + v }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
