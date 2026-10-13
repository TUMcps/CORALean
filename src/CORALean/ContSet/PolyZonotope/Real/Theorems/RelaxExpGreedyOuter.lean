import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpMultiOuter
import Mathlib.Order.BourbakiWitt

/-!
# Relaxing along a selection over-approximates

`[1, Thm. 2]`, whose soundness content is one sentence — the greedy relaxation
encloses because `[1, Thm. 1]` does — and whose remainder is a complexity claim
that belongs to a `Complexity/Space/` development rather than here.

So the whole of it is the loop, and that the loop encloses *whatever* the
selection: an enclosure composes with an enclosure, and each step is
`relaxExpMulti_outer`, which asks nothing of the pair it merges. There is
nothing to prove about the greedy edge, the threshold or the tie-break, and
nothing here that could be made false by choosing differently — which is why the
heuristic can be replaced without touching this file.

`relaxExpMulti_outer` rather than `relaxExp_outer` is what makes the induction a
line: under the pairwise version every step would owe a similarity hypothesis
about a set the previous step built.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxation loop over-approximates, at every selection and every number
of steps. -/
theorem PolyZonotope.relaxExpGreedy_outer
    (sel : (pZ : PolyZonotope α) →
      Option ((d : ℕ) × (Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2))))
    (n : ℕ) (pZ : PolyZonotope α) :
    pZ.construct ⊆ (PolyZonotope.relaxExpGreedy sel n pZ).construct := by -- --- PROOF ---
  induction n generalizing pZ with
  | zero => exact subset_rfl
  | succ n ih =>
    -- the step the selection names, or none, in which case the loop is over
    show pZ.construct ⊆ ((sel pZ).elim pZ
      fun sp => PolyZonotope.relaxExpGreedy sel n (pZ.relaxExpMulti sp.2)).construct
    cases sel pZ with
    | none => exact subset_rfl
    | some sp => exact subset_trans (pZ.relaxExpMulti_outer sp.2) (ih _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
