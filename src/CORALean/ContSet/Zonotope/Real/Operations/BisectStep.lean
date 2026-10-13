import CORALean.ContSet.Zonotope.Real.Operations.SplitPivot
import Mathlib.Analysis.Convex.Segment

/-!
# One pass of the dichotomic search of [1, Alg. 4]

Lines 15-26, the body of `while |G| > 1`: split `G` at the pivot `s` (line 16), form the sum `s₁`
of the lower half (line 17), and keep the lower half if `[P; P + s₁]` meets `L_γ` (lines 18-20),
otherwise move to the upper half from `P + s₁` (lines 21-24). The state is `(P, G, s)`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 4] lines 15-26: one iteration of the loop on the state `(P, G, s)`. -/
noncomputable def Zonotope.bisectStep (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) (right : Bool)
    (st : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2) : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2 :=
  if 1 < st.2.1.card then                                              -- line 15
    let split := Z.splitPivot right st.2.1 st.2.2                      -- line 16
    let s₁ := ∑ i ∈ split.1, (2 : ℝ) • Z.G i                           -- line 17
    if (segment ℝ st.1 (st.1 + s₁) ∩ {z | z 0 = γ}).Nonempty then      -- line 18
      (st.1, split.1, s₁)                                              -- lines 19-20
    else (st.1 + s₁, split.2, st.2.2 - s₁)                             -- lines 22-24
  else st

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
