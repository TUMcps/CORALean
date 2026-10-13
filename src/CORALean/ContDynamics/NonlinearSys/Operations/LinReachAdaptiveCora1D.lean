import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptErrLoopCora1D
import CORALean.ContDynamics.NonlinearSys.Operations.OptimalDeltatCora

/-!
# `linReachAdaptiveCora1D`, the first step of CORA's `linReach_adaptive` in one dimension

CORA's `@nonlinearSys/linReach_adaptive.m` (`alg = 'lin-adaptive'`, `postProcessing`'s
`decrFactor = 0.9`, `redFactor = 0.0005`, `zetaphi(3) = 0.68`), first step (`options.i == 1`),
from a point `x0`, without inputs, line by line along the path whose tuned step is the finite
horizon `0.01 (tFinal - tStart)`: run 1 at the horizon (`veryfirststep`), run 1 at `decrFactor`
times it, the gain `varphi` against `zetaphi`, `aux_optimaldeltat` (`optimalDeltatCora`), and, the
tuned step being the horizon (`timeStepequalHorizon`), run 2 at `decrFactor` times it; the result
is the horizon run's sets. Each run is `linearize` (`p = x0 + f(x0)·Δt/2`), `initReach_adaptive`
and the error loop `adaptErrLoopCora1D` over `abstrErrAdaptiveCora1D`. Sets are intervals as
`(inf, sup)`.

Only `A = f'(p) = 0` is modelled (else `none`): `aux_expmtie_adaptive` stops at `eta = 2` with
`E = F = 0`, so `Rhom_tp = Rdelta + Δt f(p)`, `Rhom = enclose(Rdelta, Rhom_tp)`, and
`errorSolution_adaptive` scales a box by `Δt`. A point start gives `tensorOrder = 2` and, by
`aux_getPowers` at `A = 0`, `minorder = 2`; a zero `trueError` makes `orders = Inf`, an indexing
error. Branches off the path (halving, a small `varphi`, a shorter tuned step) and running out of
`fuel` are `none`. The result is `(Rti, Rtp, options.Δt)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first step of CORA's `linReach_adaptive` (`'lin'`) for `ẋ = f(x)` from the point `x0`,
Jacobian `f'`, interval Hessian `hessIv`: `(Rti, Rtp, timeStep)`, or `none` off the path on which
the tuned time step is the finite horizon. -/
noncomputable def NonlinearSys.linReachAdaptiveCora1D (f f' : ℝ → ℝ) (hessIv : ℝ → ℝ → ℝ × ℝ)
    (x0 tStart tFinal : ℝ) (fuel : ℕ) : Option ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) :=
  let decrFactor : ℝ := 9 / 10                            -- options.decrFactor = 0.90
  let redFactor : ℝ := 5 / 10000                          -- options.redFactor = 0.0005
  let zetaphi : ℝ := 68 / 100                             -- options.zetaphi(options.minorder+1)
  let timeStep_h := (tFinal - tStart) * (1 / 100)         -- options.Δt = (tF - tS) * 0.01
  let finitehorizon := timeStep_h                         -- finitehorizon = options.Δt
  -- run 1 at the finite horizon (veryfirststep)
  let p_h := x0 + f x0 * (1 / 2) * timeStep_h             -- p.x = cx + f0prev*0.5*timeStep
  let f0_h := f p_h                                       -- f0 = nlnsys.mFile(p.x,p.u)
  let A_h := f' p_h                                       -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A_h ≠ 0 then none else
  let zetaP_h := Real.exp (A_h * timeStep_h)              -- zetaP = exp(trace(linsys.A*timeStep))
  let Rdelta_h := x0 - p_h                                -- Rdelta = Rstart + (-p.x)
  let Rlintp_h := Rdelta_h + timeStep_h * f0_h            -- Rhom_tp = eAt*Rstart + Rtrans
  let Rlinti_h := (min Rdelta_h Rlintp_h, max Rdelta_h Rlintp_h) -- Rhom = enclose(Rstart,Rhom_tp)
  -- aux_checkIfHessianConst, on the very first call (error_adm = 0, so Rmax = Rlinti)
  let totalInt₀ := (Rlinti_h.1 + p_h, Rlinti_h.2 + p_h)   -- totalInt_x = IH_x + p.x
  let H₀ := hessIv totalInt₀.1 totalInt₀.2                -- H = nlnsys.hessian(totalInt_x,..)
  let c₀ := (totalInt₀.1 + totalInt₀.2) / 2               -- c = center(I)
  let r₀ := (totalInt₀.2 - totalInt₀.1) / 2               -- r = rad(I)
  let H_test := hessIv (c₀ - r₀ * (11 / 10)) (c₀ + r₀ * (11 / 10)) -- obj.hessian(enlarge(..,1.1))
  let hessianConst : Option ℝ :=                          -- options.isHessianConst
    if H₀ = H_test then some (max |H₀.1| |H₀.2|) else none --   = all(H{i} == H_test{i})
  let Φ_h := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p_h
    (Rlinti_h.1 - timeStep_h * error_adm, Rlinti_h.2 + timeStep_h * error_adm) -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ_h fuel 1 0 0 with -- error_adm = error_adm_horizon = 0
  | none => none                                          -- ~Lconverged: halve timeStep
  | some trueError_h =>
  if trueError_h = 0 then none else                       -- aux_getPowers: orders = Inf
  let Rerror_h := timeStep_h * trueError_h                -- Rerror = errorSolution_adaptive(..)
  let abstrerr_h := Rerror_h                              -- abstrerr = sum(abs(generators(Rerror)))
  -- run 1 at decrFactor times the finite horizon
  let timeStep₁ := decrFactor * timeStep_h                -- options.Δt = decrFactor*timeStep
  let error_adm₁ := decrFactor * trueError_h              -- error_adm = decrFactor * trueError
  let p₁ := x0 + f x0 * (1 / 2) * timeStep₁               -- p.x = cx + f0prev*0.5*timeStep
  let f0₁ := f p₁                                         -- f0 = nlnsys.mFile(p.x,p.u)
  let A₁ := f' p₁                                         -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A₁ ≠ 0 then none else
  let Rdelta₁ := x0 - p₁                                  -- Rdelta = Rstart + (-p.x)
  let Rlintp₁ := Rdelta₁ + timeStep₁ * f0₁                -- Rhom_tp = eAt*Rstart + Rtrans
  let Rlinti₁ := (min Rdelta₁ Rlintp₁, max Rdelta₁ Rlintp₁) -- Rhom = enclose(Rstart,Rhom_tp)
  let Φ₁ := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p₁
    (Rlinti₁.1 - timeStep₁ * error_adm, Rlinti₁.2 + timeStep₁ * error_adm) -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ₁ fuel 1 error_adm₁ 0 with
  | none => none                                          -- ~Lconverged: halve timeStep
  | some trueError₁ =>
  let abstrerr₁ := timeStep₁ * trueError₁                 -- abstrerr = sum(abs(generators(Rerror)))
  let varphi := abstrerr₁ / abstrerr_h                    -- varphi = max(errRatio(~isnan(..)))
  if varphi < zetaphi then none else                      -- decrease time step size
  let timeStep₂ := NonlinearSys.optimalDeltatCora 0 Rerror_h -- aux_optimaldeltat(Rstart,Rerror_h,
    finitehorizon varphi zetaP_h decrFactor redFactor     --   finitehorizon,varphi,zetaP_h,options)
  if timeStep₂ ≠ finitehorizon then none else             -- if options.Δt == finitehorizon
  -- run 2 (timeStepequalHorizon)
  let timeStep₃ := timeStep₂ * decrFactor                 -- options.Δt*options.decrFactor
  let p₃ := x0 + f x0 * (1 / 2) * timeStep₃               -- p.x = cx + f0prev*0.5*timeStep
  let f0₃ := f p₃                                         -- f0 = nlnsys.mFile(p.x,p.u)
  let A₃ := f' p₃                                         -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A₃ ≠ 0 then none else
  let Rdelta₃ := x0 - p₃                                  -- Rdelta = Rstart + (-p.x)
  let Rlintp₃ := Rdelta₃ + timeStep₃ * f0₃                -- Rhom_tp = eAt*Rstart + Rtrans
  let Rlinti₃ := (min Rdelta₃ Rlintp₃, max Rdelta₃ Rlintp₃) -- Rhom = enclose(Rstart,Rhom_tp)
  let Φ₃ := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p₃
    (Rlinti₃.1 - timeStep₃ * error_adm, Rlinti₃.2 + timeStep₃ * error_adm) -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ₃ fuel 1 0 0 with -- error_adm = zeros
  | none => none                                          -- ~Lconverged: halve timeStep
  | some _ =>
  -- timeStepequalHorizon: Rti = Rti_h + linx_h, Rtp = Rtp_h + linx_h, Rerror = Rerror_h
  some ((Rlinti_h.1 + p_h - Rerror_h, Rlinti_h.2 + p_h + Rerror_h), -- Rti = Rti + Rerror
    (Rlintp_h + p_h - Rerror_h, Rlintp_h + p_h + Rerror_h),        -- Rtp = Rtp + Rerror
    finitehorizon)                                        -- options.Δt = finitehorizon

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
