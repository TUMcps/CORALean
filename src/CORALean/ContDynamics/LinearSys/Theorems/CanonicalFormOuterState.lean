module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# The canonical form holds every state input

`Ax + B(uVec + u) + c + E w` with `u ∈ U`, `w ∈ W` is `Ax + u'` [1] with `u' - u_` in `U_`: the
centred sets carry what moves, `u_` the rest. Outer only, as the set operations are.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalForm_state_outer (sys : LinearSys ℝ n) (U : S sys.m)
    (uVec : Vec ℝ sys.m) (W : S sys.r) (V : S sys.s) (vVec : Vec ℝ sys.s) {u : Vec ℝ sys.m}
    (hu : u ∈ construct U) {w : Vec ℝ sys.r} (hw : w ∈ construct W) :
    sys.B *ᵥ (uVec + u) + sys.c + sys.E *ᵥ w - (sys.canonicalForm U uVec W V vVec).2.2.1
      ∈ construct (sys.canonicalForm U uVec W V vVec).2.1 := by -- --- PROOF ---
  -- the offset cancels, leaving `B (u - centerU) + E (w - centerW)`
  have heq : sys.B *ᵥ (uVec + u) + sys.c + sys.E *ᵥ w - (sys.canonicalForm U uVec W V vVec).2.2.1
      = sys.B *ᵥ (u - Recentre.centre U) + sys.E *ᵥ (w - Recentre.centre W) := by
    simp only [LinearSys.canonicalForm, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  rw [heq]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- `B (u - centerU)` is in `B U₀`
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (Recentre.sub_centre_mem_recentre hu)
  · -- `E (w - centerW)` is in `E W₀`
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (Recentre.sub_centre_mem_recentre hw)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
