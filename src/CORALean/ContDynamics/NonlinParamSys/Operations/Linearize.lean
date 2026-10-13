import CORALean.ContDynamics.NonlinParamSys.Definitions.Linearized
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.Global.Jacobian

/-!
# `NonlinParamSys.linearize`

CORA's `nonlinParamSys/linearize` [1], the branch for uncertain parameters in a box `paramInt`
(`isa(params.paramInt,'interval')`). The dynamics are split as `parametricDynamicFile` does
(`derivatives`, `aux_parametric`): the part without parameters, `f(x, u, 0)`, and for each
parameter the difference `f(x, u, e_i) - f(x, u, 0)` to the unit vector, which is `f_i` in
`f = f_0 + ∑ p_i f_i`. The box is normalized, `f_0 + ∑ c_i f_i` with generators `r_i f_i`, and the
Jacobians in `x` and `u` the same way, giving `zf`, `zA` and `zB`. Nothing checks that `f` is
affine in `p`; the split is right only if it is. The numeric-`p` branch is `NonlinearSys.linearize`
at the fixed `p` and the `'linRem'` option adds `lin_error2dAB`; neither is carried.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linearization of `sys` about `(xs, us)` over the parameter box `paramInt`. -/
noncomputable def NonlinParamSys.linearize (sys : NonlinParamSys n m q) (xs : Vec ℝ n)
    (us : Vec ℝ m) (paramInt : Interval (Vec ℝ q)) : NonlinParamSys.Linearized n m q :=
  let c := paramInt.center                                          -- center(params.paramInt)
  let r := paramInt.radius                                          -- rad(params.paramInt)
  let e := fun i : Fin q => (Pi.single i 1 : Vec ℝ q)               -- unitvector(i,numParams)
  let f0 := sys.f xs us 0                                           -- f0_3D(:,:,1)
  let fi := fun i => sys.f xs us (e i) - f0                         -- f0_3D(:,:,i+1)
  let A0 := jacobianMat (fun x => sys.f x us 0) xs                  -- A(:,:,1)
  let Ai := fun i => jacobianMat (fun x => sys.f x us (e i)) xs - A0   -- A(:,:,i+1)
  let B0 := jacobianMat (fun u => sys.f xs u 0) us                  -- B(:,:,1)
  let Bi := fun i => jacobianMat (fun u => sys.f xs u (e i)) us - B0   -- B(:,:,i+1)
  { xs := xs, us := us, ps := c                                     -- p.x, p.u, p.p
    zf := ⟨q, f0 + ∑ i, c i • fi i, fun i => r i • fi i⟩            -- zf
    zA := ⟨q, A0 + ∑ i, c i • Ai i, fun i => r i • Ai i⟩            -- zA
    zB := ⟨q, B0 + ∑ i, c i • Bi i, fun i => r i • Bi i⟩ }          -- zB

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
