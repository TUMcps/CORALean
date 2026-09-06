import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpMultiOuter

/-!
# Relaxing along a selection over-approximates at the stored columns

The exact layer's induction, over this layer's steps. Each step is
`relaxExpMulti_outer`, which already charges its two roundings to the box, so
composing steps composes enclosures and the loop owes nothing further.

The selection is as free here as it is over ℝ, and freer in practice: this is
the layer where an edge weight can actually be compared, so it is the layer a
greedy rule runs in — and none of that reaches the guarantee, which holds at any
selection and any number of steps.

The box grows one interval per step and is never re-read by the loop, so a
caller wanting fewer steps asks for fewer rather than for a different rule.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxation loop over-approximates, at every selection and every number
of steps. -/
theorem PolyZonotope.relaxExpGreedy_outer
    (sel : (PZ : PolyZonotope 𝕋 n) →
      Option ((d : ℕ) × (Split (Fin PZ.h) into (Fin d) and (Fin 2))))
    (m : ℕ) (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ (PolyZonotope.relaxExpGreedy sel m PZ).construct := by -- --- PROOF ---
  induction m generalizing PZ with
  | zero => exact subset_rfl
  | succ m ih =>
    -- the step the selection names, or none, in which case the loop is over
    show PZ.construct ⊆ ((sel PZ).elim PZ
      fun sp => PolyZonotope.relaxExpGreedy sel m (PZ.relaxExpMulti sp.2)).construct
    cases sel PZ with
    | none => exact subset_rfl
    | some sp => exact subset_trans (PZ.relaxExpMulti_outer sp.2) (ih _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
