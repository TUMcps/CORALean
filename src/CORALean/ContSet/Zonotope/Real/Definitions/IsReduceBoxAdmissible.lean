module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# When a reduction order meets an admissible bound

`IsReduceBoxAdmissible Z B o`: `reduceBox` at order `o` stays inside `B`, what
[1] tunes the reduction order to. Set containment rather than a real-valued
bound, and needs no soundness side condition to go with it: `reduceBox` is
total, and `reduceBox_eq_ofPoint` already gives an order meeting any `B`
containing `0`. `reduceBoxOrder` names the least order meeting it.

## Inputs
* `Z` – zonotope
* `B` – admissible bound
* `o` – order

## Output
* `Prop` that box reduction at `o` stays inside `B`

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order meeting the admissible bound `B`: `reduceBox` at that order stays
inside it. -/
def Zonotope.IsReduceBoxAdmissible (Z : Zonotope (Vec ℝ n)) (B : Set (Vec ℝ n)) (o : ℕ) : Prop :=
  (Z.reduceBox o).construct ⊆ B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
