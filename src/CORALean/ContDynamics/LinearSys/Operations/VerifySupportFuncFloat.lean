module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifySupportResult
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.BalanceScalesFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.EnergyGrowthFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.LogNormUpFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportPassFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyTimeSetdiff
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `LinearSys.verifySupportFuncFloat`, CORA's `priv_verifyRA_supportFunc`, made sound

Reach-avoid verification of `ẋ = Ax`, `y = C x` from `X₀ = ⟨c, G⟩` against `(C_s y)_q ≤ d_q`
over `[0, t_f]`. CORA's loop: the step starts at `t_f / ⌈t_f / (t_f/100)⌉`; a pass
(`LinearSys.verifySupportPassFloat`) that cannot enclose its matrices shrinks it by `0.2`; one
that falsifies stops; otherwise the verified steps leave the unverified times, the horizon
shrinks to the last of them and the step by `0.2`, until none is left or the step is below
`minStep`. Departures for soundness: the rows `C_s C` are not normalized and come from a
bracket (their error is `E₀`); the times are exact, and no unverified time is dropped
(`LinearSys.verifyTimeSetdiff`); the initial set is checked from below.

## Inputs
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Cs` – float rows of the halfspaces in the output
* `Cm` – float output matrix
* `d` – float offsets of the halfspaces
* `tFinal` – float time horizon
* `minStep` – float smallest step size
* `fuel` – largest number of passes

## Output
* the verdict and CORA's statistics of the run
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

/-- A pass's verified steps leave the unverified times: step `k` of `Δt` is `[kΔt, (k+1)Δt]`. -/
@[step_of LinearSys.verifySupportFuncFloat]
def LinearSys.step_verifySupportUnsat (Δt : ℚ) (flags : List (Fin r → Bool))
    (U : Fin r → List (ℚ × ℚ)) : Fin r → List (ℚ × ℚ) :=
  let V := Vector.ofFn fun q => (flags.zipIdx).foldl (fun W f =>
    if f.1 q then LinearSys.verifyTimeSetdiff W (f.2 * Δt) ((f.2 + 1) * Δt) else W) (U q)
  fun q => V[q.val]'q.isLt

/-- The growth bound `‖S⁻¹e^{tA}S‖ ≤ κ e^{tμ}`: the energy weight's at the rate `1/t_f` if it is
accepted (`MatExp.energyGrowthFloat`), else `κ = 1` and the log norm. -/
@[step_of LinearSys.verifySupportFuncFloat]
def LinearSys.step_verifySupportGrowth (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (tFinal : 𝕋) : 𝕋 × 𝕋 :=
  let ρ := divUp one tFinal
  match MatExp.energyGrowthFloat A s ρ with
  | some κ => (κ, ρ)
  | none => (one, MatExp.logNormUpFloat A s)

/-- The passes from `Δt` while `fuel` lasts, with the unverified times `U` up to `tf`. -/
@[step_of LinearSys.verifySupportFuncFloat]
def LinearSys.step_verifySupportLoop (A : Mat 𝕋 n n) (s c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (v : Vec 𝕋 n) (βX κ μ : 𝕋) (ℓ₀ : Mat 𝕋 r n) (E₀ d : Vec 𝕋 r) (T : ℚ) (minStep : 𝕋) :
    ℕ → 𝕋 → (Fin r → List (ℚ × ℚ)) → ℚ → ℕ → LinearSys.VerifySupportResult 𝕋 r
  | 0, Δt, _, _, it => ⟨none, it, Δt, 0, none⟩
  | fuel + 1, Δt, U, tf, it =>
    let shrink := divUp one (nsmulUp 5 one)                              -- 0.2
    let N := ⌈tf / ToRat.toRat Δt⌉₊                                      -- the steps to tf
    match LinearSys.verifySupportPassFloat A s c G v βX κ μ ℓ₀ E₀ d Δt N T with
    | .notConverged => LinearSys.step_verifySupportLoop A s c G v βX κ μ ℓ₀ E₀ d T minStep fuel
        (mulUp Δt shrink) U tf (it + 1)
    | .noBound => ⟨none, it + 1, Δt, N, none⟩
    | .falsified k q => ⟨some false, it + 1, Δt, N, some ((k : ℚ) * ToRat.toRat Δt, q)⟩
    | .decided flags =>
      let U' := LinearSys.step_verifySupportUnsat (ToRat.toRat Δt) flags U
      if (List.finRange r).all fun q => (U' q).isEmpty then ⟨some true, it + 1, Δt, N, none⟩
      else
        let tf' := (List.finRange r).foldl (fun t q => (U' q).foldl (fun t iv => max t iv.2) t) 0
        let Δt' := mulUp Δt shrink
        if ltStrict Δt' minStep then ⟨none, it + 1, Δt, N, none⟩
        else LinearSys.step_verifySupportLoop A s c G v βX κ μ ℓ₀ E₀ d T minStep fuel Δt' U' tf'
          (it + 1)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `priv_verifyRA_supportFunc` for `ẋ = Ax`: the run constants, the initial set's check,
the first step size, then the passes. -/
def LinearSys.verifySupportFuncFloat (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Cs : Mat 𝕋 r p) (Cm : Mat 𝕋 p n) (d : Vec 𝕋 r) (tFinal minStep : 𝕋) (fuel : ℕ) :
    LinearSys.VerifySupportResult 𝕋 r :=
  let s := MatExp.balanceScalesFloat A                                   -- the scales
  let g := LinearSys.step_verifySupportGrowth A s tFinal                 -- κ e^{tμ}
  let v := (Interval.point fun i =>                                      -- ≥ |c| + Σⱼ |gⱼ|
    addUp (absolute (c i)) (sumUp fun j => absolute (G i j))).materialise.sup
  let βX := maximum zero (maximumOver fun i => divUp (v i) (s i))      -- ≥ |xᵢ|/sᵢ over X₀
  let L := (Interval.matMul (Interval.point Cs) (Interval.point Cm)).materialiseMat -- [C_s C]
  let ℓ₀ := L.sup                                                        -- the rows
  let E₀ := (Interval.point fun q =>                                     -- their errors
    sumUp fun j => mulUp (subUp (L.sup q j) (L.inf q j)) (s j)).materialise.sup
  let T := ToRat.toRat tFinal
  if !(List.finRange n).all fun i => ltStrict zero (s i) then ⟨none, 0, zero, 0, none⟩ else
  match (List.finRange r).find? fun q =>                                 -- X₀ itself
      ltStrict zero (subDown (LinearSys.verifySupportDownFloat c G βX (ℓ₀ q) (E₀ q)) (d q)) with
  | some q => ⟨some false, 0, zero, 0, some (0, q)⟩
  | none =>
    let Δt₀ := divUp tFinal (nsmulUp 100 one)                            -- t_f / 100
    let Δt := divUp tFinal (intUp ⌈ToRat.toRat (divUp tFinal Δt₀)⌉)      -- t_f / ⌈t_f / Δt₀⌉
    LinearSys.step_verifySupportLoop A s c G v βX g.1 g.2 ℓ₀ E₀ d T minStep fuel Δt
      (fun _ => [(0, T)]) T 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
