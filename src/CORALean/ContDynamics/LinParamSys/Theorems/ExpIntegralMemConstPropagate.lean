module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec

@[expose] public section

/-!
# `constPropagate` holds what a constant input contributes by `t_k`, at every member

The split case of [1, Alg. 1] (an input set missing the origin, which [1, Sec. 3.3] leaves out),
carried window by window: by induction on `k`,
`expIntegral A 0 = 0` starts it, and `expIntegral_add_mulVec` (`a := t_k`,
`b := Δt`) carries `t_k`'s value across one more window, `e^{AΔt}` a member of
`expEnclosure Δt η` and `Δt`'s own contribution a member of
`constInputSolution Δt η ũ` at its right end.

## Inputs
* `sys` – system
* `Δt` – window length
* `η` – Taylor order
* `A` – system matrix member
* `uc` – constant input

## Hypotheses
* `hΔt` – window length positive
* `hε` – order admissible
* `hA` – `A` lies in the matrix set

## Conclusion
* the contribution by every window start lies in the propagated set

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
variable [∀ n, CompactSet (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by `t_k = k Δt`, at any member `A` of
`sys.A`, lies in `constPropagate Δt η ũ k`, at an order admissible for `Δt`. -/
theorem LinParamSys.expIntegral_mem_constPropagate (sys : LinParamSys ℐ n)
    {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) (uc : Vec ℝ n) : -- --- CONCL ---
    ∀ k : ℕ,
    MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ uc
      ∈ construct (sys.constPropagate (S := S) Δt η uc k)
  | 0 => by
    have hz : MatExp.expIntegral A (((0 : ℕ) : ℝ) * Δt) = 0 := by simp [MatExp.expIntegral]
    rw [hz, Matrix.zero_mulVec]
    exact OfPoint.mem_ofPoint 0
  | k + 1 => by
    have hrec := Real.MatExp.expIntegral_add_mulVec A uc (a := (k : ℝ) * Δt) (b := Δt)
      (by positivity) hΔt.le
    have htk : ((k + 1 : ℕ) : ℝ) * Δt = (k : ℝ) * Δt + Δt := by push_cast; ring
    rw [htk, hrec]
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (Mtimes.mtimes_outer _ _ (Set.mem_biUnion (sys.exp_mem_expEnclosure Δt η hA)
        (Set.mem_image_of_mem _ (sys.expIntegral_mem_constPropagate hΔt η hε hA uc k))))
      (sys.expIntegral_mem_constInputSolution hΔt η hε hA uc hΔt.le (le_refl Δt)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
