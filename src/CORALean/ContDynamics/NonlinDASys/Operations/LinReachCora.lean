module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinErrorCora
public import CORALean.ContDynamics.LinearSys.Operations.OneStep
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `NonlinDASys.linReachCora`

CORA's `@nonlinDASys/linReach.m` for one step as printed, at the error-loop pass that ends it:
`priv_linearize` builds `Ã = A - CF⁻¹D`, `B̃ = B - CF⁻¹E` and `f0 = f(z*) - CF⁻¹g(z*)`,
`oneStep` runs the linearized system from `Rinit - x*` without the error, and the error set
`Verror` of `priv_linError_mixed_noInt` (`NonlinDASys.linErrorCora`, `+ CF_inv` on the algebraic
part) enters afterwards as `Rerror = particularSolution_timeVarying(linsys, Verror)`, added to
both sets once they are moved back by `x*`. This is the step `initReach` (line 66) and `post`
take with CORA's default `alg = 'lin'`, `tensorOrder = 2`.

The `while` loop that grows the assumed error until it covers the computed one is not run:
its last pass computes `Verror` over a deviation zonotope `R^z_Δ` (CORA's `R_xyu`, reduced)
and the Hessians' midpoints and radii over that pass's box, and these are the arguments
`R_Δ`, `Hd_c`, `Hd_Δ`, `Ha_c`, `Ha_Δ`, as in `linErrorCora`. The algebraic set `Rti_y` and
the split decision are left out. `particularSolution_timeVarying` is `inputSolution`, the
time-varying input part `oneStep` takes too. With `NonlinDASys.linError` in `Verror`'s place,
this is `NonlinDASys.linReach` up to where the error enters (there, in `oneStep`'s input).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `nonlinDASys/linReach` as printed, the error set
`priv_linError_mixed_noInt`'s (`linErrorCora`): the time-point and the time-interval set. -/
noncomputable def NonlinDASys.linReachCora (f₀ : Vec ℝ n) (g₀ : Vec ℝ p) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (C : Mat ℝ n p) (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p)
    (xs : Vec ℝ n) (us : Vec ℝ m) (Rinit : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m))
    (Hd_c Hd_Δ : Fin n → Mat ℝ q q) (Ha_c Ha_Δ : Fin p → Mat ℝ q q) (R_Δ : Zonotope (Vec ℝ q))
    (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  let CF_inv : Mat ℝ n p := C * F_inv                                     -- CF_inv
  let f0 : Vec ℝ n := f₀ - CF_inv *ᵥ g₀                                  -- f0 = linParams.uTrans
  let A_lin : Mat ℝ n n := A - CF_inv * D                                 -- A_lin
  let B_lin : Mat ℝ n m := B - CF_inv * E                                 -- B_lin
  let U_lin : Zonotope (Vec ℝ n) :=                                       -- linParams.U
    (U.plus (Zonotope.ofPoint (-us))).mtimes B_lin
  let linsys : LinearSys ℝ n := LinearSys.canonical A_lin  -- linearSys(A_lin, 1)
  let Rdelta : Zonotope (Vec ℝ n) := Rinit.plus (Zonotope.ofPoint (-xs))  -- Rinit - p.x
  let R := linsys.oneStep (S := 𝒵) Rdelta U_lin f0 Δt η                  -- [Rtp,Rti] = oneStep
  let Verror : Zonotope (Vec ℝ n) :=                                    -- priv_linError_mixed_noInt
    NonlinDASys.linErrorCora Hd_c Hd_Δ Ha_c Ha_Δ CF_inv R_Δ
  let Rerror : Zonotope (Vec ℝ n) :=                                      -- Rerror
    linsys.inputSolution (S := 𝒵) Δt η Verror
  let Rti : Zonotope (Vec ℝ n) := R.2.plus (Zonotope.ofPoint xs)          -- Rti + p.x
  let Rtp : Zonotope (Vec ℝ n) := R.1.plus (Zonotope.ofPoint xs)          -- Rtp + p.x
  (Rtp.plus Rerror, Rti.plus Rerror)                                      -- + Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
