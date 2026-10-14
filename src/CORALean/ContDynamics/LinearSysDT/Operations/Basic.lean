module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.OutputEq.OutputEq

@[expose] public section

/-!
# `ContDynamics/LinearSysDT/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ==================================  `LinearSysDT.outputEq`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The output equation `y = C x + D u + k`, read off the system as stored.

The noise term `F v` stays with the system: `OutputEq.outputSetNoise` takes `sys.F` beside it. -/
def LinearSysDT.outputEq (sys : LinearSysDT 𝕋 n) : OutputEq 𝕋 n sys.m sys.q :=
  ⟨sys.C, sys.D, sys.k⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
