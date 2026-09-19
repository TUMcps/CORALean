import CORALean.ContDynamics.LinearSys.MatExp.AffineDynamicsError
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Shift

/-!
# `H(t_{k+1})`, `H(τ_k)` and `Ĥ(τ_k)`, the three sets of [1, Prop. 1]

The affine dynamics `ẋ = Ax + ũ` of Line 9 of [1, Alg. 1]: `affineTimePointNext` is the
propagated `H(t_{k+1}) = e^{AΔt}H(t_k) ⊕ P^u(Δt)` with `P^u(Δt) = A^{-1}(e^{AΔt}-I_n)ũ` taken
as `MatExp.expIntegral`, the power series [1] itself falls back on when `A` is singular;
`affineTimeIntervalSolution` is the exact tube [1, Prop. 1] displays; and
`affineTimeIntervalOuter` is its eq. (22) enclosure `comb(H(t_k),H(t_{k+1})) ⊕ C`, with `C` the
curvature set `AffineDynamicsError.lean` already spells.

[1] writes the tube's flow map `e^{At}` at absolute time `t ∈ τ_k = [t_k,t_{k+1}]` while every
other set in the display is relative to `t_k`; read literally the two do not compose, so the
elapsed time `t - t_k ∈ [0,Δt]` is what this definition runs over.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `H(t_{k+1}) = e^{AΔt}H(t_k) ⊕ A^{-1}(e^{AΔt}-I_n)ũ`, Lines 6-7 of [1, Alg. 1]. -/
noncomputable def MatExp.affineTimePointNext (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) : Zonotope (Vec ℝ n) :=
  (Zonotope.mtimes (exp (Δt • A)) H).shift (-(MatExp.expIntegral A Δt).mulVec ũ)

/-- [1, Prop. 1]'s exact time-interval solution `H(τ_k)` of the affine dynamics `ẋ = Ax + ũ`,
over the elapsed times `[0,Δt]` of the step. -/
noncomputable def MatExp.affineTimeIntervalSolution (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ t ∈ Set.Icc (0:ℝ) Δt, ∃ x ∈ H.construct,
    y = (exp (t • A)).mulVec x + (MatExp.expIntegral A t).mulVec ũ}

/-- [1]'s eq. (22) `Ĥ(τ_k) = comb(H(t_k),H(t_{k+1})) ⊕ C`, Line 9 of [1, Alg. 1]. -/
noncomputable def MatExp.affineTimeIntervalOuter (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  (H.linComb (MatExp.affineTimePointNext A H ũ Δt)).plus
    (MatExp.curvatureEnclosure A H ũ Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
