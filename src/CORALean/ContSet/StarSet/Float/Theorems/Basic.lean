module

public import CORALean.ContSet.StarSet.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet
public import CORALean.ContSet.StarSet.Real.Operations.Basic

@[expose] public section

/-!
# `ContSet/StarSet/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- ============================  `StarSet.LinPred.nominal_addRows`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The rows added in floats are the exact rows added, read as reals. -/
theorem StarSet.LinPred.nominal_addRows (p : StarSet.LinPred 𝕋 m) (rs : List ((Fin m → 𝕋) × 𝕋)) :
    (p.addRows rs).nominal
      = p.nominal.addRows (rs.map fun r => (fun k => toReal (r.1 k), toReal r.2)) := by
  simp [StarSet.LinPred.addRows, CORALean.Real.StarSet.LinPred.addRows, List.map_append]


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
