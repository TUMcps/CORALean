module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifySupportOutcome
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionInputFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyBoxDotDownFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyBoxDotUpFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputInnerFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputOuterFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyCurvatureUpFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportDownFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportUpFloat
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.Global.Float.Exp
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifySupportPassFloat`, one pass of CORA's `priv_verifyRA_supportFunc`, made sound

`N` steps of `Δt` for `ẋ = Ax + u`, `u(t) ∈ u₀ + M [-1, 1]^p`, from `X₀ = ⟨c, G⟩` against
`ℓ_q x ≤ d_q`. CORA's `ℓ_{k+1} = ℓ_k e^{AΔt}` uses a point `expm`; here `ℓ̃_{k+1} = ℓ̃_k D̃`
(`MatExp.expBallFloat`) errs by at most `Y (E₀ + Σ_{j<k} δ_j)`, `Y ≥ κ e^{μ⁺NΔt}`. A time point
gets CORA's distance from above and below, a step the larger end plus the curvature term.
The input (`LinearSys.verifyInputSolutionFloat`) adds along `ℓ̃_i`, `i < k`, the constant part's
`w` (`Pu`) from above and below, the varying part's outer support (`overPU`) over the step, its
inner one (`underPU`) to the falsification, and `G u₀` to the curvature term. A step below `0` is
verified; a time point within `T` above `0` falsifies, the first in CORA's scan order.

## Inputs
* `A` – float system matrix
* `s` – positive float scales
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `v` – float upper bound of `|c| + Σⱼ |gⱼ|`
* `βX` – float bound of the scaled entries of the initial set
* `κ` – float factor of the balanced growth bound `κ e^{tμ}` of `e^{tA}`
* `μ` – float rate of that bound
* `u₀` – float box of the constant input, as a column
* `MU` – float box of the generators of the input
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m p r : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The input's terms along `ℓ̃_k` with the error `E`: `ℓ' w` from above and below, `ℓ' g` from
above, the outer and the held inner support of one step's varying input. -/
@[step_of LinearSys.verifySupportPassFloat]
def LinearSys.step_verifySupportInputFloat (I : LinearSys.VerifyInputSolution 𝕋 n p)
    (g : Interval (Mat 𝕋 n 1)) (βw βg βU : 𝕋) (ℓ : Vec 𝕋 n) (E : 𝕋) : 𝕋 × 𝕋 × 𝕋 × 𝕋 × 𝕋 :=
  (LinearSys.verifyBoxDotUpFloat I.w βw ℓ E, LinearSys.verifyBoxDotDownFloat I.w βw ℓ E,
    LinearSys.verifyBoxDotUpFloat g βg ℓ E, LinearSys.verifyInputOuterFloat I.V I.ρ βU ℓ E,
    LinearSys.verifyInputInnerFloat I.Vs I.ρ βU ℓ E)

/-- The steps `k, …, k + fuel - 1`: the rows `ℓ̃_k`, the error sums `acc_k`, the upper distances
at `t_k`, the input's sums over `i < k` (`ℓ' w` up and down, outer, inner) in, the flags of the
steps so far (latest first). -/
@[step_of LinearSys.verifySupportPassFloat]
def LinearSys.step_verifySupportStepsFloat (s c : Vec 𝕋 n) (G : Mat 𝕋 n m) (βX : 𝕋)
    (wc : Interval (Vec 𝕋 n)) (WG : Interval (Mat 𝕋 n m)) (wr : Vec 𝕋 n) (βF : 𝕋)
    (I : LinearSys.VerifyInputSolution 𝕋 n p) (g : Interval (Mat 𝕋 n 1)) (βw βg βU : 𝕋)
    (D : Mat 𝕋 n n) (rD Y : 𝕋) (d : Vec 𝕋 r) (Δt : 𝕋) (T : ℚ) :
    ℕ → ℕ → Mat 𝕋 r n → Vec 𝕋 r → Vec 𝕋 r → Vec 𝕋 r → Vec 𝕋 r → Vec 𝕋 r → Vec 𝕋 r →
      List (Fin r → Bool) → LinearSys.VerifySupportOutcome r
  | _, 0, _, _, _, _, _, _, _, flags => .decided flags.reverse
  | k, fuel + 1, ℓ, acc, aff, cw, cwd, cov, cin, flags =>
    let E := fun q => mulUp Y (acc q)                                    -- the errors at t_k
    let cb := fun q => LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (E q)
    let inp := fun q => LinearSys.step_verifySupportInputFloat I g βw βg βU (ℓ q) (E q)
    let cw' := (Interval.point fun q => addUp (cw q) (inp q).1).materialise.sup  -- Σ_{i≤k} ℓ'w
    let cwd' := (Interval.point fun q => addDown (cwd q) (inp q).2.1).materialise.sup
    let cov' := (Interval.point fun q => addUp (cov q) (inp q).2.2.2.1).materialise.sup
    let cin' := (Interval.point fun q => addDown (cin q) (inp q).2.2.2.2).materialise.sup
    let ℓUp := (Interval.point fun q j => dotUp (ℓ q) fun i => D i j).materialiseMat.sup
    let ℓDn := fun q j => dotDown (ℓ q) fun i => D i j                   -- ℓ̃_k D̃ from below
    let gap := fun q => sumUp fun j => mulUp (subUp (ℓUp q j) (ℓDn q j)) (s j)
    let δ := fun q => addUp (mulUp (sumUp fun j => mulUp (absolute (ℓ q j)) (s j)) rD) (gap q)
    let acc' := (Interval.point fun q => addUp (acc q) (δ q)).materialise.sup  -- acc_{k+1}
    let E' := fun q => mulUp Y (acc' q)
    let aff' := (Interval.point fun q =>                                 -- the distances at t_{k+1}
      subUp (addUp (LinearSys.verifySupportUpFloat c G βX (ℓUp q) (E' q)) (cw' q)) (d
          q)).materialise.sup
    let low := fun q => subDown (addDown (addDown
      (LinearSys.verifySupportDownFloat c G βX (ℓUp q) (E' q)) (cwd' q)) (cin' q)) (d q)
    let flag := fun q => ltStrict (addUp (addUp (addUp (maximum (aff q) (aff' q)) (cb q))
      (inp q).2.2.1) (cov' q)) zero
    match (List.finRange r).find? fun q => ltStrict zero (low q) with
    | some q =>
      if ((k + 1 : ℕ) : ℚ) * ToRat.toRat Δt ≤ T then .falsified (k + 1) q
      else LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF I g βw βg βU D rD Y d Δt T
        (k + 1) fuel ℓUp acc' aff' cw' cwd' cov' cin' (flag :: flags)
    | none => LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF I g βw βg βU D rD Y d Δt T
        (k + 1) fuel ℓUp acc' aff' cw' cwd' cov' cin' (flag :: flags)

/-- The input's boxes at `Δt`: none without an input, else `LinearSys.verifyInputSolutionFloat`,
and the box of `G u₀` (none without a constant input). -/
@[step_of LinearSys.verifySupportPassFloat]
def LinearSys.step_verifySupportInputBoxesFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋)
    (u₀ : Interval (Mat 𝕋 n 1)) (MU : Interval (Mat 𝕋 n p)) :
    Option (LinearSys.VerifyInputSolution 𝕋 n p × Interval (Mat 𝕋 n 1)) :=
  let isZero := fun x : 𝕋 => le x zero && le zero x
  let hasU := !(List.finRange n).all fun l => isZero (u₀.inf l 0) && isZero (u₀.sup l 0)
  let hasM := !(List.finRange n).all fun l => (List.finRange p).all fun c =>
    isZero (MU.inf l c) && isZero (MU.sup l c)
  let I := if hasU || hasM then LinearSys.verifyInputSolutionFloat A s Δt u₀ MU
    else some ⟨Interval.point fun _ _ => zero, [], Interval.point fun _ _ => zero, fun _ => zero⟩
  let g := if hasU then (MatExp.verifyCorrectionInputFloat A s Δt).map fun G =>
      (Interval.matMul G.2 u₀).materialiseMat
    else some (Interval.point fun _ _ => zero)
  match I, g with
  | some I, some g => some (I, g)
  | _, _ => none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One pass: the correction matrix, the exponential and the input's boxes at `Δt`, the growth
bound `Y` over `N Δt`, the curvature data, then the `N` steps from `ℓ₀`. -/
def LinearSys.verifySupportPassFloat (A : Mat 𝕋 n n) (s c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (v : Vec 𝕋 n) (βX κ μ : 𝕋) (u₀ : Interval (Mat 𝕋 n 1)) (MU : Interval (Mat 𝕋 n p))
    (ℓ₀ : Mat 𝕋 r n) (E₀ d : Vec 𝕋 r) (Δt : 𝕋) (N : ℕ) (T : ℚ) :
    LinearSys.VerifySupportOutcome r :=
  match MatExp.verifyCorrectionStateFloat A s Δt with
  | none => .notConverged
  | some (_, F) =>
  match MatExp.expBallFloat A s Δt with
  | none => .notConverged
  | some (D, rD) =>
  match LinearSys.step_verifySupportInputBoxesFloat A s Δt u₀ MU with
  | none => .notConverged
  | some (I, g) =>
  let Fc := (Interval.point fun j k =>                                   -- F's center
    addUp (F.inf j k) (half (subUp (F.sup j k) (F.inf j k)))).materialiseMat.sup
  let Fr := (Interval.point fun j k =>                                   -- F's radius about it
    maximum (subUp (F.sup j k) (Fc j k)) (subUp (Fc j k) (F.inf j k))).materialiseMat.sup
  let wc : Interval (Vec 𝕋 n) := (⟨mulVecDown Fc c, mulVecUp Fc c⟩ : Interval _).materialise
  let WG : Interval (Mat 𝕋 n m) := (⟨matMulDown Fc G, matMulUp Fc G⟩ : Interval _).materialiseMat
  let wr := (Interval.point (mulVecUp Fr v)).materialise.sup             -- ≥ F_r v
  let Fm := fun j k => addUp (absolute (Fc j k)) (Fr j k)                -- ≥ |F|
  let βF := maximum zero (maximumOver fun i => divUp (mulVecUp Fm v i) (s i))
  let βw := maximum zero (maximumOver fun l =>                          -- ≥ |w_l| / s_l
    divUp (sumUp fun c => I.w.magnitudeMat l c) (s l))
  let βg := maximum zero (maximumOver fun l => divUp (sumUp fun c => g.magnitudeMat l c) (s l))
  let βU := maximum zero (maximumOver fun l => divUp (addUp (I.V.foldl (fun acc X =>
    addUp acc (sumUp fun c => X.magnitudeMat l c)) zero) (I.ρ l)) (s l))  -- the varying input's
  let a := mulUp (maximum μ zero) (mulUp (nsmulUp N one) Δt)            -- ≥ μ⁺ N Δt
  if ltStrict zero Δt && le a ((fun x => addDown x x)^[29] one) then
    let Y := maximum one (mulUp κ (expUp 30 a))                          -- ≥ κ e^{μ⁺ N Δt}
    let aff₀ := (Interval.point fun q =>                                 -- the distances at t_0
      subUp (addUp (LinearSys.verifySupportUpFloat c G βX (ℓ₀ q) (mulUp Y (E₀ q))) zero)
        (d q)).materialise.sup
    LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF I g βw βg βU D rD Y d Δt T 0 N
      ℓ₀ E₀ aff₀ (fun _ => zero) (fun _ => zero) (fun _ => zero) (fun _ => zero) []
  else .noBound

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
