module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# The canonical form holds every output noise

`D(uVec + u) + k + F(vVec + v)` with `u ∈ U`, `v ∈ V` is `v'` with `v' - v_` in `V_` [1], where
`V_ = D U + F (V - centerV)`: the input's contribution to the output is a noise of its own,
not tied to the state input. Outer only.

## Inputs
* `sys` – linear system
* `U` – input set
* `uVec` – input offset
* `W` – disturbance set
* `V` – noise set
* `vVec` – noise offset
* `u` – input value
* `v` – noise value

## Hypotheses
* `hu` – input lies in its set
* `hv` – noise lies in its set

## Conclusion
* the canonical output set holds the output of every input and noise

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
variable [∀ n, Recenter (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalForm_output_outer (sys : LinearSys ℝ n) (U : S sys.m)
    (uVec : Vec ℝ sys.m) (W : S sys.r) (V : S sys.s) (vVec : Vec ℝ sys.s) {u : Vec ℝ sys.m}
    (hu : u ∈ construct U) {v : Vec ℝ sys.s} (hv : v ∈ construct V) : -- --- CONCL ---
    sys.D *ᵥ (uVec + u) + sys.k + sys.F *ᵥ (vVec + v)
        - (sys.canonicalForm U uVec W V vVec).2.2.2.2
      ∈ construct (sys.canonicalForm U uVec W V vVec).2.2.2.1 := by -- --- PROOF ---
  -- the offset cancels, leaving `D u + F (v - centerV)`
  have heq : sys.D *ᵥ (uVec + u) + sys.k + sys.F *ᵥ (vVec + v)
        - (sys.canonicalForm U uVec W V vVec).2.2.2.2
      = sys.D *ᵥ u + sys.F *ᵥ (v - Recenter.center V) := by
    simp only [LinearSys.canonicalForm, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  rw [heq]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- `D u` is in `D (U₀ + centerU)`, `u` being `(u - centerU) + centerU`
    have hu' := Plus.plus_outer _ _ (Set.add_mem_add (Recenter.sub_center_mem_recenter hu)
      (OfPoint.mem_ofPoint (Recenter.center U)))
    rw [sub_add_cancel] at hu'
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ hu'
  · -- `F (v - centerV)` is in `F V₀`
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (Recenter.sub_center_mem_recenter hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
