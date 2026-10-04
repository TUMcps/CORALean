import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Operations.IsBox

/-!
# `ZonoBundle.isIntervalCora`

What `@zonoBundle/representsa_` computes for the type `'interval'`: `n == 1 || aux_isInterval(zB,
tol)`, where `aux_isInterval` is `true` in dimension one and for an empty set, and otherwise loops
`for i = 1:zB.parallelSets` over `representsa_(zB.Z{1}, 'interval', tol)`. The loop variable `i` is
never used: it tests the first member `Z{1}` `parallelSets` times, so a bundle whose *first* member
is a box passes whatever the others are. Read from the source, not run (`IsCoraCounterexample`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's test: `n = 1`, or an empty set, or every pass of the loop finds `Z{1}` a box. -/
def ZonoBundle.isIntervalCora (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) : Prop :=
  n = 1 ∨ zB.construct = ∅ ∨ ∀ _i : Fin zB.k, (zB.Z ⟨0, hk⟩).IsBox


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
