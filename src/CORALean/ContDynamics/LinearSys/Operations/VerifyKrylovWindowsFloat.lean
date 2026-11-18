module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyKrylovWindow
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.CarryMinFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ResidualNormFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowErrorOkFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyKrylovWindowsFloat`, the restart windows of CORA.cpp's Krylov verification

CORA.cpp's `KrylovWindows` (`priv_krylov_windows.cpp`) for `z(t) = e^{tA'} w` on the plan of its
tuning (order `k` and steps `m` of `Δt₀` per window). A window restarts `Krylov.arnoldiFloat` of
`A'` from the float start `x`; its local error is [1, Thm. 3] (`Krylov.errorBoundFloat`) at
`L = m Δt₀`. The start's error `C` is carried by `g ≥ e^{L μ_A⁺}` (`g C + local`); with a
certificate `(P, L, a)` of `A'` that passes `Krylov.windowErrorOkFloat`, the window's error is the
smaller of that and the Lyapunov carry `Krylov.windowErrorBoundFloat` of the earlier windows'
transition errors (`Krylov.carryMinFloat`). The next start is `ν V D̃ e₁` rounded up. The plan
search and the certificate's solve are tuning and not checked.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold of Arnoldi
* `A` – float system matrix
* `w` – float direction
* `Δt₀` – float step size of the windows
* `plan` – order and steps of every window
* `cert` – Lyapunov certificate `(P, L, a)` of `A'`, if any

## Output
* the windows, or none (an order below 1, an inexact or too long window, no ball)

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- One window of order `k` and `m` steps from the start `x` with the error `C`: the window (its
Gershgorin error), the next start with its error, the length, the local and the transition error. -/
@[step_of LinearSys.verifyKrylovWindowsFloat]
def LinearSys.step_verifyKrylovWindowFloat (p q : ℕ) (εb : 𝕋) (At : Mat 𝕋 n n) (Δt₀ : 𝕋)
    (x : Vec 𝕋 n) (C : 𝕋) :
    ℕ → ℕ → Option (LinearSys.VerifyKrylovWindow 𝕋 n × Vec 𝕋 n × 𝕋 × 𝕋 × 𝕋 × 𝕋)
  | 0, _ => none
  | k + 1, m =>
  let ν := normUp p x                                                    -- ‖x‖₂
  let st := Krylov.arnoldiFloat p εb At x ν (k + 1)                     -- V, H
  let μA := Krylov.quadBoundUp At                                        -- ≥ x'A'x / x'x
  let L := nsmulUp m Δt₀                                                 -- m Δt₀
  let res := fun j => Krylov.residualNormFloat p At st.1 st.2 j
  let μ := maximum zero (maximum μA (Krylov.quadBoundUp fun i j : Fin (k + 1) => st.2 i j))
  let ok := le L (nsmulDown m Δt₀) && le zero Δt₀ &&
    le (mulUp L μ) (nsmulDown (2 ^ (q - 1)) one) &&
    le (mulUp L (maximum μA zero)) ((fun y => addDown y y)^[29] one)
  if !ok then none else
  let loc := Krylov.errorBoundFloat p q μA res x ν st.1 st.2 (k + 1) L  -- the local error
  let g := expUp 30 (mulUp L (maximum μA zero))                         -- ≥ e^{L μ_A⁺}
  let V : Mat 𝕋 n (k + 1) := fun i j => (st.1 j)[i]
  let H : Mat 𝕋 (k + 1) (k + 1) := fun i j => st.2 i j
  match MatExp.expBallFloat H (fun _ => one) L with
  | none => none
  | some (D, rD) =>
    -- the next start `ν V D̃ e₁`, from below and above
    let lo := fun i => Interval.mulLo ν ν (dotDown (V i) fun l => D l 0)
      (dotUp (V i) fun l => D l 0)
    let hi := fun i => Interval.mulHi ν ν (dotDown (V i) fun l => D l 0)
      (dotUp (V i) fun l => D l 0)
    let start := mulUp (mulUp (absolute ν) rD) (sumUp fun l => normUp p fun i => V i l)
    let gap := normUp p fun i => subUp (hi i) (lo i)
    let err := addUp (mulUp g C) loc
    some (⟨k + 1, V, H, ν, m, err⟩, hi, addUp err (addUp start gap), L, loc,
      addUp loc (addUp start gap))

/-- The error of window `N = Δts.length` of length `L` and local error `loc` after the windows of
the lengths `Δts` and transition errors `εs`: the Lyapunov carry where its certificate holds and
it is smaller, else the Gershgorin error `errG`. -/
@[step_of LinearSys.verifyKrylovWindowsFloat]
def LinearSys.step_verifyKrylovCarryFloat (p q : ℕ) (c : Option (Krylov.LyapunovCertificateFloat 𝕋))
    (Δts εs : List 𝕋) (L loc errG : 𝕋) : 𝕋 :=
  let Δt := fun j => (Δts ++ [L]).getD j zero                              -- the lengths
  let εw := fun j => (εs ++ [loc]).getD j zero                             -- and the errors
  match c with
  | some c => if Krylov.windowErrorOkFloat q c Δt Δts.length then
      Krylov.carryMinFloat errG (Krylov.windowErrorBoundFloat p q c Δt εw Δts.length)
    else errG
  | none => errG

/-- The windows of the plan in order from the start `x` with the error `C`, after the windows of
the lengths `Δts` and transition errors `εs`. -/
@[step_of LinearSys.verifyKrylovWindowsFloat]
def LinearSys.step_verifyKrylovWindowsLoopFloat (p q : ℕ) (εb : 𝕋) (At : Mat 𝕋 n n) (Δt₀ : 𝕋)
    (c : Option (Krylov.LyapunovCertificateFloat 𝕋)) :
    List (ℕ × ℕ) → Vec 𝕋 n → 𝕋 → List 𝕋 → List 𝕋 →
      Option (List (LinearSys.VerifyKrylovWindow 𝕋 n))
  | [], _, _, _, _ => some []
  | (k, m) :: plan, x, C, Δts, εs =>
    match LinearSys.step_verifyKrylovWindowFloat p q εb At Δt₀ x C k m with
    | none => none
    | some (W, x', C', L, loc, ε) =>
      let err := LinearSys.step_verifyKrylovCarryFloat p q c Δts εs L loc W.err
      (LinearSys.step_verifyKrylovWindowsLoopFloat p q εb At Δt₀ c plan x' C' (Δts ++ [L])
        (εs ++ [ε])).map ({ W with err := err } :: ·)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows of `e^{tA'} w` on the plan, from `w` with no error. -/
def LinearSys.verifyKrylovWindowsFloat (p q : ℕ) (εb : 𝕋) (A : Mat 𝕋 n n) (w : Vec 𝕋 n)
    (Δt₀ : 𝕋) (plan : List (ℕ × ℕ)) (cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋)) :
    Option (List (LinearSys.VerifyKrylovWindow 𝕋 n)) :=
  let At : Mat 𝕋 n n := fun i j => A j i                                 -- A'
  let c := cert.map fun (P, L, a) => Krylov.lyapunovCertificateFloat At P L a
  LinearSys.step_verifyKrylovWindowsLoopFloat p q εb At Δt₀ c plan w zero [] []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
