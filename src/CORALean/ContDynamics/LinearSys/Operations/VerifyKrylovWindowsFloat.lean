module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyKrylovWindow
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ResidualNormFloat
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
`L = m Δt₀`, and the start's error `C` is carried by `g ≥ e^{L μ_A⁺}`, so the window's error is
`g C + local`. The next start is `ν V D̃ e₁` rounded up (`D̃` the ball of `e^{LH}`), with
`C' = g C + local + |ν| r Σ ‖v_l‖₂ + ‖gap‖₂`. The plan search is tuning and not checked; the
Lyapunov carry, which only makes the error smaller, is not used. `L` must be exact (`m Δt₀` the
same rounded up and down), which it is at nearest.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold of Arnoldi
* `A` – float system matrix
* `w` – float direction
* `Δt₀` – float step size of the windows
* `plan` – order and steps of every window

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

/-- One window of order `k` and `m` steps from the start `x` with the error `C`: the window and the
next start with its error, or none. -/
@[step_of LinearSys.verifyKrylovWindowsFloat]
def LinearSys.step_verifyKrylovWindowFloat (p q : ℕ) (εb : 𝕋) (At : Mat 𝕋 n n) (Δt₀ : 𝕋)
    (x : Vec 𝕋 n) (C : 𝕋) : ℕ → ℕ → Option (LinearSys.VerifyKrylovWindow 𝕋 n × Vec 𝕋 n × 𝕋)
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
    some (⟨k + 1, V, H, ν, m, err⟩, hi, addUp err (addUp start gap))

/-- The windows of the plan in order from the start `x` with the error `C`. -/
@[step_of LinearSys.verifyKrylovWindowsFloat]
def LinearSys.step_verifyKrylovWindowsLoopFloat (p q : ℕ) (εb : 𝕋) (At : Mat 𝕋 n n) (Δt₀ : 𝕋) :
    List (ℕ × ℕ) → Vec 𝕋 n → 𝕋 → Option (List (LinearSys.VerifyKrylovWindow 𝕋 n))
  | [], _, _ => some []
  | (k, m) :: plan, x, C =>
    match LinearSys.step_verifyKrylovWindowFloat p q εb At Δt₀ x C k m with
    | none => none
    | some (W, x', C') =>
      (LinearSys.step_verifyKrylovWindowsLoopFloat p q εb At Δt₀ plan x' C').map (W :: ·)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows of `e^{tA'} w` on the plan, from `w` with no error. -/
def LinearSys.verifyKrylovWindowsFloat (p q : ℕ) (εb : 𝕋) (A : Mat 𝕋 n n) (w : Vec 𝕋 n)
    (Δt₀ : 𝕋) (plan : List (ℕ × ℕ)) : Option (List (LinearSys.VerifyKrylovWindow 𝕋 n)) :=
  let At : Mat 𝕋 n n := fun i j => A j i                                 -- A'
  LinearSys.step_verifyKrylovWindowsLoopFloat p q εb At Δt₀ plan w zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
