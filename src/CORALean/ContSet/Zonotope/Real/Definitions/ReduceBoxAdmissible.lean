import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

/-!
# When a reduction order meets an admissible bound

`ReduceBoxAdmissible Z B o`: `reduceBox` at order `o` stays inside `B`, what
[1] tunes the reduction order to. Set containment rather than a real-valued
bound, and needs no soundness side condition to go with it: `reduceBox` is
total, and `reduceBox_eq_ofPoint` already gives an order meeting any `B`
containing `0`. `reduceBoxOrder` names the least order meeting it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
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
def Zonotope.ReduceBoxAdmissible (Z : Zonotope (Vec ℝ n)) (B : Set (Vec ℝ n)) (o : ℕ) : Prop :=
  (Z.reduceBox o).construct ⊆ B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
