module

public import CORALean.ContDynamics.NonlinDASys.Operations.CompLocalErrorCora
public import CORALean.ContDynamics.LinearSys.Operations.OneStep
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `NonlinDASys.linReachCompCora`

CORA's `@nonlinDASys/linReach.m` for one step as printed on its compositional branch: with
`options.index` set and `tensorOrder == 2` (ll. 91-99) the error set `Verror` is the
`errorTotal` of `priv_linError_mixed_noInt_comp`, `Σ_i index{i}.X' * reduce(error{i})`
(ll. 163-178), each `error{i}` the subsystem's own `NonlinDASys.compLocalErrorCora` with its
local `Csub*pinv(Fsub)`. The rest is `NonlinDASys.linReachCora`: `priv_linearize`'s `Ã`, `B̃`,
`f0`, `oneStep` from `Rinit - x*`, `Rerror = particularSolution_timeVarying(linsys, Verror)`
added to both sets moved back by `x*`.

As in `linReachCora`, the `while` loop is not run: its accepting pass's per-subsystem zonotopes
`R_xyu` (l. 104) and Hessian midpoints and radii (ll. 116-123, over that pass's box) are
arguments. All `k` subsystems have the same sizes `nx`, `ny`, `nz` (CORA's may differ); every
`index{i}.X` is taken nonempty (l. 165). `reduce(·, 'girard', options.ρ)` is
`Zonotope.reduce`. The loop-only outputs `errorTotal_x`, `errorTotal_y`, `Rtotal_y` and the
split decision are left out.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m k nx ny nz : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `nonlinDASys/linReach` as printed with `options.index` set, the error set
`priv_linError_mixed_noInt_comp`'s `errorTotal`: the time-point and the time-interval set. -/
noncomputable def NonlinDASys.linReachCompCora (f₀ : Vec ℝ n) (g₀ : Vec ℝ p) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (C : Mat ℝ n p) (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p)
    (xs : Vec ℝ n) (us : Vec ℝ m) (Rinit : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m))
    (X : Fin k → Mat ℝ nx n) (Hf_mid Hf_rad : Fin k → Fin nx → Mat ℝ nz nz)
    (Hg_mid Hg_rad : Fin k → Fin ny → Mat ℝ nz nz) (Csub : Fin k → Mat ℝ nx ny)
    (Fsub : Fin k → Mat ℝ ny ny) (R_xyu : Fin k → Zonotope (Vec ℝ nz)) (zonotopeOrder : ℕ)
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
  let error : Fin k → Zonotope (Vec ℝ nx) := fun i =>                     -- error{iSys}, l. 167
    (NonlinDASys.compLocalErrorCora (Hf_mid i) (Hf_rad i) (Hg_mid i) (Hg_rad i) (Csub i)
      (Fsub i) (R_xyu i)).reduce zonotopeOrder
  let errorTotal₀ : Zonotope (Vec ℝ n) := Zonotope.ofPoint 0              -- zeros, l. 56
  let errorTotal : Zonotope (Vec ℝ n) :=                                  -- l. 171
    (List.finRange k).foldl (fun acc i => acc.plus ((error i).mtimes (X i)ᵀ)) errorTotal₀
  let Verror : Zonotope (Vec ℝ n) := errorTotal.reduce zonotopeOrder      -- reduce, l. 178
  let Rerror : Zonotope (Vec ℝ n) :=                                      -- Rerror
    linsys.inputSolution (S := 𝒵) Δt η Verror
  let Rti : Zonotope (Vec ℝ n) := R.2.plus (Zonotope.ofPoint xs)          -- Rti + p.x
  let Rtp : Zonotope (Vec ℝ n) := R.1.plus (Zonotope.ofPoint xs)          -- Rtp + p.x
  (Rtp.plus Rerror, Rti.plus Rerror)                                      -- + Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
