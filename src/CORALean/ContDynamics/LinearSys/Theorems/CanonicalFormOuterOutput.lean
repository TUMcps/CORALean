module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm

@[expose] public section

/-!
# The canonical form holds every output noise

`D(uVec + u) + k + F(vVec + v)` with `u ∈ U`, `v ∈ V` is `v'` with `v' - v_` in `V_` [1], where
`V_ = D U + F (V - centerV)`: the input's contribution to the output is a noise of its own,
not tied to the state input. Outer only.

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

theorem LinearSys.canonicalForm_output_outer (sys : LinearSys ℝ n) (B : Mat ℝ n m)
    (c : Vec ℝ n) (out : OutputEq ℝ n m r) (k : Vec ℝ r) (E : Mat ℝ n q) (F : Mat ℝ r s)
    (U : S m) (uVec : Vec ℝ m) (W : S q) (V : S s) (vVec : Vec ℝ s) {u : Vec ℝ m}
    (hu : u ∈ construct U) {v : Vec ℝ s} (hv : v ∈ construct V) :
    out.D *ᵥ (uVec + u) + k + F *ᵥ (vVec + v)
        - (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.2.2.2
      ∈ construct (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.2.2.1 := by -- --- PROOF ---
  -- the offset cancels, leaving `D u + F (v - centerV)`
  have heq : out.D *ᵥ (uVec + u) + k + F *ᵥ (vVec + v)
        - (sys.canonicalForm B c out k E F U uVec W V vVec).2.2.2.2.2
      = out.D *ᵥ u + F *ᵥ (v - Recentre.centre V) := by
    simp only [LinearSys.canonicalForm, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  rw [heq]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- `D u` is in `D (U₀ + centerU)`, `u` being `(u - centerU) + centerU`
    have hu' := Plus.plus_outer _ _ (Set.add_mem_add (Recentre.sub_centre_mem_recentre hu)
      (OfPoint.mem_ofPoint (Recentre.centre U)))
    rw [sub_add_cancel] at hu'
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ hu'
  · -- `F (v - centerV)` is in `F V₀`
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (Recentre.sub_centre_mem_recentre hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
