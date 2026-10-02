import CORALean.HybridDynamics.Definitions.Transition
import CORALean.HybridDynamics.Definitions.NonlinearReset

/-!
# `Transition.toNonlinearReset`

A transition's affine reset `x ↦ W x + w` as a nonlinear reset, which ignores its input: CORA's
`linearReset` is a `nonlinearReset` with a function that happens to be affine.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Transition.toNonlinearReset (e : Transition G L 𝕋 n) : NonlinearReset n 0 n where
  f := fun x _ => e.reset x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
