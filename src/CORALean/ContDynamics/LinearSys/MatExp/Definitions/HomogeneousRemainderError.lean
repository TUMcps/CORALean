module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.Global.Err

@[expose] public section

/-!
# `ε_H([t_i,t_i+Δt_i])`, eq. (21), and the two correction interval matrices it is built from

[1]'s eq. (21): `ε_H([t_i,t_{i+1}]) = err(e^{At_i} F_x(Δt_i,η_i) X_0 ⊕ e^{At_i} F_u(Δt_i,η_i) c_u)`,
the error of the homogeneous solution over the `i`-th step: `err` of `HR^+([0,Δt])` (eq. (19)),
carried to `t_i` by `e^{At_i}` as eq. (2) requires. `err` is `r(box(·))` of [1, Prop. 1].
`F_x` and `F_u` are eq. (17)-(18) as printed: a Minkowski sum over `k` of the scalar interval
`[(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0]` times the matrix `A^k/k!` (for `F_u`, `A^{k-1}/k!` and
`k` up to `η+1`), plus the interval matrix `E(Δt,η)` of eq. (15)-(16) (for `F_u`, `E(Δt,η)Δt`).
`MatExp.corrCoeff k` is that coefficient; `MatExp.correctionMatrix` is *not* this `F_x`: it is
CORA's own enclosure, no `F_u` beside it.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order

## Output
* matrices the state correction interval matrix contains

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (17): `F_x(Δt,η) = ⊕_{k=2}^η [(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0] A^k/k! ⊕ E(Δt,η)`,
as the set of matrices it contains. -/
noncomputable def MatExp.stateCorrectionSet (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Set (Mat ℝ n n) :=
  (∑ k ∈ Finset.Icc 2 η, (fun r : ℝ => r • (((Nat.factorial k : ℝ))⁻¹ • A ^ k)) ''
      Set.Icc (MatExp.corrCoeff k * Δt ^ k) 0)
    + MatExp.expRemainderInterval A Δt η

/-- [1]'s eq. (18):
`F_u(Δt,η) = ⊕_{k=2}^{η+1} [(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0] A^{k-1}/k! ⊕ E(Δt,η)Δt`,
as the set of matrices it contains. -/
noncomputable def MatExp.inputCorrectionSet (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Set (Mat ℝ n n) :=
  (∑ k ∈ Finset.Icc 2 (η + 1), (fun r : ℝ => r • (((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1))) ''
      Set.Icc (MatExp.corrCoeff k * Δt ^ k) 0)
    + Δt • MatExp.expRemainderInterval A Δt η

/-- `e^{At_i} F_x(Δt,η) X_0 ⊕ e^{At_i} F_u(Δt,η) c_u`, the set eq. (21) takes `err` of: eq. (19)'s
`HR^+([0,Δt])` carried to the `i`-th step. -/
noncomputable def MatExp.homogeneousRemainderSet (A : Mat ℝ n n) (ti : ℝ) (X₀ : Set (Vec ℝ n))
    (cu : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (fun x => (exp (ti • A)).mulVec x) ''
      Set.image2 (fun M x => M.mulVec x) (MatExp.stateCorrectionSet A Δt η) X₀
    + (fun x => (exp (ti • A)).mulVec x) ''
      ((fun M : Mat ℝ n n => M.mulVec cu) '' MatExp.inputCorrectionSet A Δt η)

/-- [1]'s eq. (21): `ε_H([t_i,t_i+Δt]) := err(e^{At_i} F_x(Δt,η) X_0 ⊕ e^{At_i} F_u(Δt,η) c_u)`. -/
noncomputable def MatExp.homogeneousRemainderError (A : Mat ℝ n n) (ti : ℝ) (X₀ : Set (Vec ℝ n))
    (cu : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  err (MatExp.homogeneousRemainderSet A ti X₀ cu Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
