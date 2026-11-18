module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyKrylovWindow
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.BalanceScalesFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionStateFloat
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyKrylovBoundsFloat`, the support bounds of CORA.cpp's Krylov verification

CORA.cpp's `Stepper::next_margin` (`priv_verify_ra_krylov.cpp`) for one direction `w`, made sound:
the bound of `w' x(t)` over every step of `ẋ = Ax + u`, `u(t) ∈ ⟨u_c, G_U⟩`, from `X₀ = ⟨c, G⟩`.
In a window `z(t) = w' e^{tA} = ν V ψ(τ) + e`, so a vector `v` has `z' v = W_v ψ + e' v`,
`W_v = ν v' V`; on a step `ψ` lies between its ends plus `[F] ψ_i`, and the input's integral
gains this step's integrand (at least `0`) times `Δt`. Departures from CORA.cpp for soundness:
`e^{HΔt}` is the ball `MatExp.expBallFloat`, whose iterates carry the scaled error
`E_{i+1} = (‖D̃‖ + r) E_i + r ‖ŷ_i‖ + gap`; a window's first step starts from its own `W_v e₁`,
not from the last window's value (another basis). The windows are given.

## Inputs
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `uc` – float center of the input set, in the state space
* `GU` – float generators of the input set, in the state space
* `w` – float direction
* `wins` – the restart windows of `w' e^{tA}`, their steps of `ratio Δt`
* `ratio` – steps of the pass per step of the windows
* `Δt` – float step size
* `N` – number of steps

## Output
* the bound of `w' x(t)` per step, or none (no enclosure, or the windows end before `N` steps)
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m p : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `[a, b]' [c, d]`, from below and above: the sums of the corner products. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovDotFloat {k : ℕ} (a b c d : Vec 𝕋 k) : 𝕋 × 𝕋 :=
  (sumDown fun l => Interval.mulLo (a l) (b l) (c l) (d l),
    sumUp fun l => Interval.mulHi (a l) (b l) (c l) (d l))

/-- The row `W_v = ν v' V` of a vector in the window, from below and above. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovRowFloat (W : LinearSys.VerifyKrylovWindow 𝕋 n) (v : Vec 𝕋 n) :
    Interval (Vec 𝕋 W.k) :=
  (⟨fun l => Interval.mulLo W.ν W.ν (dotDown v fun r => W.V r l) (dotUp v fun r => W.V r l),
    fun l => Interval.mulHi W.ν W.ν (dotDown v fun r => W.V r l)
      (dotUp v fun r => W.V r l)⟩ : Interval (Vec 𝕋 W.k)).materialise

/-- `Σ_l |R_l| r_l`, rounded up: what `R` makes of a vector within `r E`. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovMagFloat {k : ℕ} (R : Interval (Vec 𝕋 k)) (r : Vec 𝕋 k) : 𝕋 :=
  sumUp fun l => mulUp (maximum (absolute (R.inf l)) (absolute (R.sup l))) (r l)

/-- The term of a vector on a step: its row's range over the step (the hull of `W_v ŷ_i` and
`W_v ŷ_{i+1}` plus `W_v [F] ŷ_i`), its upper end if `signed` (a center) or its magnitude (a
generator), plus the iterates' errors `a_v E_{i+1} + b_v E_i`. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovTermFloat {k : ℕ} (signed : Bool) (R : Interval (Vec 𝕋 k))
    (s g y y' : Vec 𝕋 k) (Fy : Interval (Vec 𝕋 k)) (E E' : 𝕋) : 𝕋 :=
  let P := LinearSys.step_verifyKrylovDotFloat R.inf R.sup y y          -- W_v ŷ_i
  let C := LinearSys.step_verifyKrylovDotFloat R.inf R.sup y' y'        -- W_v ŷ_{i+1}
  let K := LinearSys.step_verifyKrylovDotFloat R.inf R.sup Fy.inf Fy.sup -- W_v [F] ŷ_i
  let lo := addDown (minimum P.1 C.1) K.1
  let hi := addUp (maximum P.2 C.2) K.2
  let ext := addUp (mulUp (LinearSys.step_verifyKrylovMagFloat R s) E')
    (mulUp (LinearSys.step_verifyKrylovMagFloat R g) E)
  addUp (if signed then hi else maximum (absolute lo) (absolute hi)) ext

/-- A window's constants at `Δt`: the scales `s` of `H`, the ball `(D̃, r)` of `e^{HΔt}`, the
scaled norm of `D̃`, the correction matrix `[F]` and `g_l ≥ Σ_m |F_lm| s_m`. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovSetupFloat (W : LinearSys.VerifyKrylovWindow 𝕋 n) (Δt : 𝕋) :
    Option (Vec 𝕋 W.k × Mat 𝕋 W.k W.k × 𝕋 × 𝕋 × Interval (Mat 𝕋 W.k W.k) × Vec 𝕋 W.k) :=
  let s := MatExp.balanceScalesFloat W.H
  if !(List.finRange W.k).all fun l => ltStrict zero (s l) then none else
  match MatExp.expBallFloat W.H s Δt, MatExp.verifyCorrectionStateFloat W.H s Δt with
  | some (D, rD), some (_, F) =>
    let nD := maximum zero (maximumOver fun l =>                         -- ≥ ‖S⁻¹ D̃ S‖
      sumUp fun j => divUp (mulUp (absolute (D l j)) (s j)) (s l))
    let g := (Interval.point fun l => sumUp fun j =>
      mulUp (maximum (absolute (F.inf l j)) (absolute (F.sup l j))) (s j)).materialise.sup
    some (s, D, rD, nD, F, g)
  | _, _ => none

/-- `L` steps of a window from `ŷ` with the error `E`, the integral `I` and the bounds so far
(latest first): `ŷ_{i+1} = D̃ ŷ_i` rounded up, `E_{i+1}`, `[F] ŷ_i`, the homogeneous bound and the
integrand from the terms, the bound `hom + I + Δt max(integrand, 0)`, `I + Δt integrand`. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovStepsFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) (uc : Vec 𝕋 n)
    (GU : Mat 𝕋 n p) (W : LinearSys.VerifyKrylovWindow 𝕋 n) (s : Vec 𝕋 W.k) (D : Mat 𝕋 W.k W.k)
    (rD nD : 𝕋) (F : Interval (Mat 𝕋 W.k W.k)) (g : Vec 𝕋 W.k) (nR nU Δt : 𝕋) :
    ℕ → Vec 𝕋 W.k → 𝕋 → 𝕋 → List 𝕋 → 𝕋 × List 𝕋
  | 0, _, _, I, out => (I, out)
  | L + 1, y, E, I, out =>
    let Dy : Interval (Vec 𝕋 W.k) := (⟨mulVecDown D y, mulVecUp D y⟩ : Interval _).materialise
    let y' := Dy.sup                                                     -- ŷ_{i+1}
    let ym := maximumOver fun l => divUp (absolute (y l)) (s l)          -- ≥ ‖S⁻¹ ŷ_i‖
    let gap := maximumOver fun l => divUp (subUp (Dy.sup l) (Dy.inf l)) (s l)
    let E' := maximum E (addUp (addUp (mulUp (addUp nD rD) E) (mulUp rD ym)) gap)  -- E_{i+1}
    let Fy : Interval (Vec 𝕋 W.k) :=                                     -- [F] ŷ_i
      (⟨fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).1,
        fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).2⟩ :
          Interval _).materialise
    let term := fun (signed : Bool) (v : Vec 𝕋 n) => LinearSys.step_verifyKrylovTermFloat signed
      (LinearSys.step_verifyKrylovRowFloat W v) s g y y' Fy E E'
    let hom := addUp (mulUp W.err nR)                                    -- x₀ ∈ ⟨c, G⟩
      (addUp (term true c) (sumUp fun j => term false fun i => G i j))
    let integrand := addUp (mulUp W.err nU)                              -- u ∈ ⟨u_c, G_U⟩
      (addUp (term true uc) (sumUp fun j => term false fun i => GU i j))
    let bound := addUp (addUp hom I) (mulUp Δt (maximum integrand zero))
    LinearSys.step_verifyKrylovStepsFloat c G uc GU W s D rD nD F g nR nU Δt L y' E'
      (addUp I (mulUp Δt integrand)) (bound :: out)

/-- The windows in order, `rem` steps left, with the input's integral `I` and the bounds so far:
each window from `e₁` with no error, for its steps times `ratio` or the steps left. -/
@[step_of LinearSys.verifyKrylovBoundsFloat]
def LinearSys.step_verifyKrylovWindowsFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) (uc : Vec 𝕋 n)
    (GU : Mat 𝕋 n p) (nR nU Δt : 𝕋) (ratio : ℕ) :
    List (LinearSys.VerifyKrylovWindow 𝕋 n) → ℕ → 𝕋 → List 𝕋 → Option (List 𝕋)
  | _, 0, _, out => some out.reverse
  | [], _ + 1, _, _ => none
  | W :: ws, rem + 1, I, out =>
    match LinearSys.step_verifyKrylovSetupFloat W Δt with
    | none => none
    | some (s, D, rD, nD, F, g) =>
      let L := min (W.steps * ratio) (rem + 1)
      let e₁ : Vec 𝕋 W.k := fun l => if l.val = 0 then one else zero
      let r := LinearSys.step_verifyKrylovStepsFloat c G uc GU W s D rD nD F g nR nU Δt L e₁ zero
        I out
      LinearSys.step_verifyKrylovWindowsFloat c G uc GU nR nU Δt ratio ws (rem + 1 - L) r.1
        r.2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds of `w' x(t)` over the `N` steps: `0` for a zero `w`, else the windows from `t = 0`
with `‖c‖₂ + Σ ‖g_j‖₂` and `‖u_c‖₂ + Σ ‖g_{U,j}‖₂` rounded up. -/
def LinearSys.verifyKrylovBoundsFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) (uc : Vec 𝕋 n)
    (GU : Mat 𝕋 n p) (w : Vec 𝕋 n) (wins : List (LinearSys.VerifyKrylovWindow 𝕋 n)) (ratio : ℕ)
    (Δt : 𝕋) (N : ℕ) : Option (List 𝕋) :=
  if !ltStrict zero Δt then none else
  if (List.finRange n).all fun i => le (w i) zero && le zero (w i) then
    some (List.replicate N zero)
  else
    let nR := addUp (normUp 30 c) (sumUp fun j => normUp 30 fun i => G i j)  -- ≥ Σ ‖·‖₂ of X₀
    let nU := addUp (normUp 30 uc) (sumUp fun j => normUp 30 fun i => GU i j)
    LinearSys.step_verifyKrylovWindowsFloat c G uc GU nR nU Δt ratio wins N zero []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
