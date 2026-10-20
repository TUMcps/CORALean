module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OneParamF
public import CORALean.ContSet.Zonotope.Real.Operations.OfOneParamPoly
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `MatExp.inputOneParam`

The partial input solution of [1, Sec. IV-B] at one parameter, its Taylor part:
`Σ_{i=0}^η Aⁱ(β) c(β) r^{i+1}/(i+1)!` with `A(β) = C + βG` and `c(β) = c_c + β g_c`, which [1] says
"can be computed similarly, as shown in the proof of Theorem 1, yielding a similar result enclosed
by a zonotope". Done here as that proof does it: the coefficient `u_k` of `βᵏ` in
`Σ_i Aⁱ(β) r^{i+1}/(i+1)!` from the `D_i`, `F_i^{(k)}`, then `w_k = u_k c_c + u_{k-1} g_c` of `βᵏ`
once `c(β)` is applied (degree `η + 1`), then `Zonotope.ofOneParamPoly`, halving the even powers.

## Inputs
* `C` – center matrix
* `G` – generator matrix
* `c_c` – input center
* `g_c` – input generator
* `r` – step length
* `η` – Taylor order

## Output
* zonotope enclosing the input solution of the one-parameter family

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def MatExp.inputOneParam (C G : Mat ℝ n n) (c_c g_c : Vec ℝ n) (r : ℝ) (η : ℕ) :
    Zonotope (Vec ℝ n) :=
  let a : ℕ → ℝ := fun i => r ^ (i + 1) / (i + 1).factorial  -- `r^{i+1}/(i+1)!`
  let u : ℕ → Mat ℝ n n := fun k =>
    if k = 0 then ∑ i ∈ Finset.range (η + 1), a i • MatExp.oneParamD C i
    else ∑ i ∈ Finset.Icc k η, a i • MatExp.oneParamF C G i k  -- `βᵏ` in `Σ a_i Aⁱ(β)`
  let w : ℕ → Vec ℝ n := fun k =>
    (if k < η + 1 then u k *ᵥ c_c else 0) + (if k = 0 then 0 else u (k - 1) *ᵥ g_c)  -- `c(β)`
  Zonotope.ofOneParamPoly w (η + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
