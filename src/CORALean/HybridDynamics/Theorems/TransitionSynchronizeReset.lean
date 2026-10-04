import CORALean.HybridDynamics.Operations.TransitionSynchronize
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeApply

/-!
# `Transition.synchronize` resets by the sum

The synchronized reset at a point is the sum of the component resets plus the pre-jump value at
`idStates`: exact.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n q k : ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The synchronized reset at a point: the sum of the component resets, plus the pre-jump value
at `idStates`. -/
theorem Transition.synchronize_reset (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (HPolytope ℝ) (L (compIdx i)) ℝ n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) (x : Vec ℝ n) (i : Fin n) :
    (Transition.synchronize compIdx t idStates locID).reset x i =
      (if i ∈ idStates then x i else 0) + ∑ j, ((t j).reset x) i := by
  simpa [Transition.synchronize, Transition.reset] using
    LinearReset.synchronize_apply (fun j => (t j).W) (fun j => (t j).w) idStates x i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
