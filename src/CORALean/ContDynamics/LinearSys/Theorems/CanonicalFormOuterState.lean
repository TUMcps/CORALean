import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm

/-!
# The canonical form holds every state input

`Ax + B(uVec + u) + c + E w` with `u ∈ U`, `w ∈ W` is `Ax + u'` [1] with `u' - u_` in `U_`: the
centred sets carry what moves, `u_` the rest. Outer only, as the set operations are.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m q r s : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalForm_state_outer (sys : LinearSys ℝ n) (B : Mat ℝ n m)
    (c : Vec ℝ n) (out : OutputEq ℝ n m r) (k : Vec ℝ r) (E : Mat ℝ n q) (F : Mat ℝ r s)
    (U : S m) (uVec : Vec ℝ m) (W : S q) (V : S s) (vVec : Vec ℝ s) {u : Vec ℝ m}
    (hu : u ∈ construct U) {w : Vec ℝ q} (hw : w ∈ construct W) :
    B *ᵥ (uVec + u) + c + E *ᵥ w
        - (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.2.1
      ∈ construct (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.1 := by -- --- PROOF ---
  -- the offset cancels, leaving `B (u - centerU) + E (w - centerW)`
  have heq : B *ᵥ (uVec + u) + c + E *ᵥ w
        - (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.2.1
      = B *ᵥ (u - Recentre.centre U) + E *ᵥ (w - Recentre.centre W) := by
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
