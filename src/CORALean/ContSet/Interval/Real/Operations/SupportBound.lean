module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CORALean.Global.StepOf

@[expose] public section

/-!
# A box answers a direction corner by corner, at `Vec ℝ n`

A one-line specialisation of `Interval.step_supportBoundEntrywise`: `Vec ℝ n`'s
`Entrywise` instance is the identity on both `entry` and `ofEntry`, so
`ofEntry (Pi.single i 1)` reduces to `Pi.single i 1` by `rfl` and the general
`val`/`le` match this type's exactly — checked, not assumed. Kept under its own
name because `Zonotope_to_HPolytope` and others may already name it.

## Inputs
* `I` – interval box
* `c` – linear functional

## Output
* support bound of the box in direction `c`
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
open Entrywise
variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- As `Interval.supportBound`, but over any `Entrywise` ambient type. -/
@[step_of Interval.supportBound]
noncomputable def Interval.step_supportBoundEntrywise [Fintype ι] [DecidableEq ι]
    (I : Interval α) (c : α →ₗ[ℝ] ℝ) : SupportBound I.construct c where
  val := ∑ i, max (c (ofEntry (Pi.single i 1)) * entry I.inf i)
                  (c (ofEntry (Pi.single i 1)) * entry I.sup i)
  le := by
    intro x hx
    have hc : c x = ∑ i, entry x i * c (ofEntry (Pi.single i 1)) := by
      conv_lhs => rw [eq_sum_single x, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hc]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    exact (Interval.mul_between_endpoints (hx i).1 (hx i).2).2

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program: the value is a sum of corner products, one per
coordinate, each attained by moving that coordinate to its far endpoint. -/
noncomputable def Interval.supportBound (I : Interval (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound I.construct c :=
  Interval.step_supportBoundEntrywise I c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
