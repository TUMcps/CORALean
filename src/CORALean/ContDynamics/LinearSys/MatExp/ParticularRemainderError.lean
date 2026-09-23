import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionOuter

/-!
# `ε_P([t_i,t_i+Δt_i])`, eq. (22)

[1]'s eq. (22): `ε_P([t_i,t_{i+1}]) = err(e^{At_i} E(Δt_i,η_i) Δt_i U)`, the error of the
inhomogeneous solution over the `i`-th step — `err` of `PR^+([0,Δt]) = E(Δt,η)ΔtU` (eq. (20))
carried to `t_i` by `e^{At_i}` as eq. (2) requires. `err` is `Global/Err.lean`'s `r(box(·))`,
[1, Prop. 1]'s radius of the smallest hypersphere at the origin enclosing the box, so this is the
Euclidean quantity [1] states and not a supremum-norm stand-in.

`E(Δt,η)` is the interval matrix `[−E_abs(Δt,η), E_abs(Δt,η)]` of eq. (15)-(16), `E_abs` being
`MatExp.expRemainderMat`, and `intervalMulVecSet` is that interval matrix acting on a set of
vectors. It reads the radius as `|E_abs|`, which is `E_abs` itself at every step `Δt ≥ 0`.

`LinearSys.timePointStepRemainderError` is a different number: a scalar upper bound at the base
step `t_i = 0`, built from a zonotope's `absBound`s and the operator-norm remainder, rather than
`err` of the set.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e^{At_i} E(Δt,η) Δt U`, the set eq. (22) takes `err` of: eq. (20)'s `PR^+([0,Δt])` carried
to the `i`-th step. -/
noncomputable def MatExp.particularRemainderSet (A : Mat ℝ n n) (ti : ℝ) (U : Set (Vec ℝ n))
    (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (fun x => (exp (ti • A)).mulVec x) '' MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η)
    (Δt • U)

/-- [1]'s eq. (22): `ε_P([t_i,t_i+Δt]) := err(e^{At_i} E(Δt,η) Δt U)`. -/
noncomputable def MatExp.particularRemainderError (A : Mat ℝ n n) (ti : ℝ) (U : Set (Vec ℝ n))
    (Δt : ℝ) (η : ℕ) : ℝ :=
  err (MatExp.particularRemainderSet A ti U Δt η)

/-- Every point of `e^{At_i} E(Δt,η) Δt U` is within an explicit multiple of `‖E(Δt,η)‖·|Δt|`
of the origin: `e^{At_i}`'s row norms times what `norm₂_le_of_mem_particularSolutionOuter`
gives the remainder block alone, the Taylor sum being empty from order `η+1`. -/
theorem MatExp.norm₂_le_of_mem_particularRemainderSet (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (Δt : ℝ) (η : ℕ) :
    ∀ y ∈ MatExp.particularRemainderSet A ti U Δt η,
      ‖y‖₂ ≤ (∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂)
        * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U) := by -- --- PROOF ---
  rintro _ ⟨z, hz, rfl⟩
  -- the remainder block is `particularSolutionOuter` with its Taylor sum started past `η`
  have hz' : z ∈ MatExp.particularSolutionOuter A U (η + 1) Δt η := by
    rw [MatExp.particularSolutionOuter, Finset.Ico_self, Finset.sum_empty, zero_add]
    exact hz
  have h := MatExp.norm₂_le_of_mem_particularSolutionOuter A hU (η + 1) Δt η z hz'
  rw [Finset.Ico_self, Finset.sum_empty, zero_add] at h
  exact (norm₂_mulVec_le _ z).trans
    (mul_le_mul_of_nonneg_left h (Finset.sum_nonneg fun i _ => norm₂_nonneg _))

/-- `e^{At_i} E(Δt,η) Δt U` is bounded whenever `U` is, which is what `err` needs of it to be
the enclosing radius rather than a junk value. -/
theorem MatExp.isBounded_particularRemainderSet (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (Δt : ℝ) (η : ℕ) :
    Bornology.IsBounded (MatExp.particularRemainderSet A ti U Δt η) := by -- --- PROOF ---
  refine isBounded_iff_forall_norm_le.mpr ⟨(∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂)
    * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U), fun y hy => ?_⟩
  -- the supremum norm is under the Euclidean one, coordinate by coordinate
  have hsup : ‖y‖ ≤ ‖y‖₂ :=
    (pi_norm_le_iff_of_nonneg (norm₂_nonneg y)).mpr fun i =>
      (Real.norm_eq_abs (y i)).trans_le (abs_le_norm₂ y i)
  exact hsup.trans (MatExp.norm₂_le_of_mem_particularRemainderSet A ti hU Δt η y hy)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
