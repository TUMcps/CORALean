module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifySupportOutcome
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyCurvatureUpFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportDownFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportUpFloat
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.Global.Float.Exp
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifySupportPassFloat`, one pass of CORA's `priv_verifyRA_supportFunc`, made sound

`N` steps of `Δt` for `ẋ = Ax` from `X₀ = ⟨c, G⟩` against `ℓ_q x ≤ d_q`. CORA propagates
`ℓ_{k+1} = ℓ_k e^{AΔt}` with a point `expm`; here `e^{AΔt}` is `MatExp.expBallFloat`'s `D̃`
within a balanced radius `r`, the rows `ℓ̃_{k+1} = ℓ̃_k D̃` are rounded up, and with
`Y ≥ e^{μ⁺NΔt}` the weighted error of `ℓ̃_k` is at most `Y (E₀ + Σ_{j<k} δ_j)`,
`δ_j = ‖ℓ̃_j‖_s r` plus the row's rounding gap (`0` at `nearest`). Each time point gets CORA's
distance from above and below (`LinearSys.verifySupportUpFloat`, `...DownFloat`), each step the
larger end plus the curvature term (`LinearSys.verifyCurvatureUpFloat`). A step below `0` is
verified; a time point within `T` above `0` falsifies, the first in CORA's scan order.

## Inputs
* `A` – float system matrix
* `s` – positive float scales
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `v` – float upper bound of `|c| + Σⱼ |gⱼ|`
* `βX` – float bound of the scaled entries of the initial set
* `μ` – float upper bound of the balanced logarithmic norm of `A`
* `ℓ₀` – float rows of the halfspaces
* `E₀` – float bounds of the weighted errors of the rows
* `d` – float offsets of the halfspaces
* `Δt` – float step size
* `N` – number of steps
* `T` – horizon of the falsification

## Output
* not converged, no growth bound, the first falsifying time point, or the verified flags per step
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m r : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The steps `k, …, k + fuel - 1`: the rows `ℓ̃_k`, the error sums `acc_k` and the upper distances
at `t_k` in, the flags of the steps so far (latest first). -/
@[step_of LinearSys.verifySupportPassFloat]
def LinearSys.step_verifySupportStepsFloat (s c : Vec 𝕋 n) (G : Mat 𝕋 n m) (βX : 𝕋)
    (wc : Interval (Vec 𝕋 n)) (WG : Interval (Mat 𝕋 n m)) (wr : Vec 𝕋 n) (βF : 𝕋)
    (D : Mat 𝕋 n n) (rD Y : 𝕋) (d : Vec 𝕋 r) (Δt : 𝕋) (T : ℚ) :
    ℕ → ℕ → Mat 𝕋 r n → Vec 𝕋 r → Vec 𝕋 r → List (Fin r → Bool) → LinearSys.VerifySupportOutcome r
  | _, 0, _, _, _, flags => .decided flags.reverse
  | k, fuel + 1, ℓ, acc, aff, flags =>
    let E := fun q => mulUp Y (acc q)                                    -- the errors at t_k
    let cb := fun q => LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (E q)
    let ℓUp := (Interval.point fun q j => dotUp (ℓ q) fun i => D i j).materialiseMat.sup
    let ℓDn := fun q j => dotDown (ℓ q) fun i => D i j                   -- ℓ̃_k D̃ from below
    let gap := fun q => sumUp fun j => mulUp (subUp (ℓUp q j) (ℓDn q j)) (s j)
    let δ := fun q => addUp (mulUp (sumUp fun j => mulUp (absolute (ℓ q j)) (s j)) rD) (gap q)
    let acc' := (Interval.point fun q => addUp (acc q) (δ q)).materialise.sup  -- acc_{k+1}
    let E' := fun q => mulUp Y (acc' q)
    let aff' := (Interval.point fun q =>                                 -- the distances at t_{k+1}
      subUp (LinearSys.verifySupportUpFloat c G βX (ℓUp q) (E' q)) (d q)).materialise.sup
    let low := fun q => subDown (LinearSys.verifySupportDownFloat c G βX (ℓUp q) (E' q)) (d q)
    let flag := fun q => ltStrict (addUp (maximum (aff q) (aff' q)) (cb q)) zero
    match (List.finRange r).find? fun q => ltStrict zero (low q) with
    | some q =>
      if ((k + 1 : ℕ) : ℚ) * ToRat.toRat Δt ≤ T then .falsified (k + 1) q
      else LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF D rD Y d Δt T (k + 1) fuel
        ℓUp acc' aff' (flag :: flags)
    | none => LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF D rD Y d Δt T (k + 1) fuel
        ℓUp acc' aff' (flag :: flags)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One pass: the correction matrix and the exponential at `Δt`, the growth bound `Y` over `N Δt`,
the curvature data, then the `N` steps from `ℓ₀`. -/
def LinearSys.verifySupportPassFloat (A : Mat 𝕋 n n) (s c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (v : Vec 𝕋 n) (βX μ : 𝕋) (ℓ₀ : Mat 𝕋 r n) (E₀ d : Vec 𝕋 r) (Δt : 𝕋) (N : ℕ) (T : ℚ) :
    LinearSys.VerifySupportOutcome r :=
  match MatExp.verifyCorrectionStateFloat A s Δt with
  | none => .notConverged
  | some (_, F) =>
  match MatExp.expBallFloat A s Δt with
  | none => .notConverged
  | some (D, rD) =>
  let Fc := (Interval.point fun j k =>                                   -- F's center
    addUp (F.inf j k) (half (subUp (F.sup j k) (F.inf j k)))).materialiseMat.sup
  let Fr := (Interval.point fun j k =>                                   -- F's radius about it
    maximum (subUp (F.sup j k) (Fc j k)) (subUp (Fc j k) (F.inf j k))).materialiseMat.sup
  let wc : Interval (Vec 𝕋 n) := (⟨mulVecDown Fc c, mulVecUp Fc c⟩ : Interval _).materialise
  let WG : Interval (Mat 𝕋 n m) := (⟨matMulDown Fc G, matMulUp Fc G⟩ : Interval _).materialiseMat
  let wr := (Interval.point (mulVecUp Fr v)).materialise.sup             -- ≥ F_r v
  let Fm := fun j k => addUp (absolute (Fc j k)) (Fr j k)                -- ≥ |F|
  let βF := maximum zero (maximumOver fun i => divUp (mulVecUp Fm v i) (s i))
  let a := mulUp (maximum μ zero) (mulUp (nsmulUp N one) Δt)            -- ≥ μ⁺ N Δt
  if ltStrict zero Δt && le a ((fun x => addDown x x)^[29] one) then
    let Y := expUp 30 a                                                  -- ≥ e^{μ⁺ N Δt}
    let aff₀ := (Interval.point fun q =>                                 -- the distances at t_0
      subUp (LinearSys.verifySupportUpFloat c G βX (ℓ₀ q) (mulUp Y (E₀ q))) (d q)).materialise.sup
    LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF D rD Y d Δt T 0 N ℓ₀ E₀ aff₀ []
  else .noBound

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
