module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyInputSolution
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyInputSolutionFloat`, one step's input in CORA's `priv_verifyRA_supportFunc`

CORA's `aux_Pu`, `aux_underPU` and `aux_overPU` for `u(t) ∈ u₀ + M [-1, 1]^m`: the constant
input's solution, the same on `M`, and the outer generators `Δt^{i+1}/(i+1)! Aⁱ M`. Order `i` is
the box `[Δt^{i+1}/(i+1)] Aⁱ/i!` (`MatExp.verifyPowerFloat`) on the boxes of `u₀` and `M`; the
series stops at the first `η ∈ [1, 74]` whose row sums are at most `eps` times those before it
(CORA's test of `overPU`), the rest is `Δt` times the scaled remainder `W` at `η - 1`. With `tight`
(the zonotope pass) it also waits until that remainder is at the level of `eps` in the scales, or
`η = 60`. The order is tuning: any `η` is sound. `none` if no `η ≤ 74` passes or `W` is not
admissible.

## Inputs
* `A` – float system matrix
* `s` – positive float scales of the remainder
* `Δt` – float step length
* `u₀` – float box of the constant input, as a column
* `M` – float box of the generators of the input
* `tight` – whether the remainder must also be at the level of `eps` (default `false`)

## Output
* the boxes of the constant input's solution, of the orders and their sum, and the remainder
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   19-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Order `i`: the box `[Δt^{i+1}/(i+1)] Aⁱ/i!` applied to the boxes of `u₀` and `M`. -/
@[step_of LinearSys.verifyInputSolutionFloat]
def LinearSys.step_verifyInputOrderFloat (A : Mat 𝕋 n n) (Δt : 𝕋) (u₀ : Interval (Mat 𝕋 n 1))
    (M : Interval (Mat 𝕋 n m)) (i : ℕ) : Interval (Mat 𝕋 n 1) × Interval (Mat 𝕋 n m) :=
  let lo := divDown (MatExp.powDown (i + 1) Δt) (nsmulUp (i + 1) one)          -- ≤ Δt^{i+1}/(i+1)
  let hi := divUp (MatExp.powUp (i + 1) Δt) (maximum one (nsmulDown (i + 1) one)) -- ≥ it
  let T := Interval.smul lo hi (MatExp.verifyPowerFloat A i)          -- ∋ Δt^{i+1}/(i+1)! Aⁱ
  ((Interval.matMul T u₀).materialiseMat, (Interval.matMul T M).materialiseMat)

/-- Row `l`'s sum of the magnitudes of an order's boxes. -/
@[step_of LinearSys.verifyInputSolutionFloat]
def LinearSys.step_verifyInputRowSumFloat (o : Interval (Mat 𝕋 n 1) × Interval (Mat 𝕋 n m))
    (l : Fin n) : 𝕋 :=
  addUp (o.1.magnitudeMat l 0) (sumUp fun c => o.2.magnitudeMat l c)

/-- Whether the remainder past order `i - 1` is at most `eps` times the orders `S` before it, in the
scales `s`: `max_l Δt Σₖ W_lk (|u₀_k| + Σ_c |M_kc|) / s_l ≤ eps max_l S_l / s_l` (tuning). -/
@[step_of LinearSys.verifyInputSolutionFloat]
def LinearSys.step_verifyInputRemainderOkFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋)
    (u₀ : Interval (Mat 𝕋 n 1)) (M : Interval (Mat 𝕋 n m)) (i : ℕ) (S : Vec 𝕋 n) (eps : 𝕋) :
    Bool :=
  match MatExp.scaledRemainderFloat A s Δt (i - 1) with
  | none => false
  | some W =>
    let x := fun k => addUp (u₀.magnitudeMat k 0) (sumUp fun c => M.magnitudeMat k c)
    let r := maximumOver fun l => divUp (mulUp Δt (sumUp fun k => mulUp (W l k) (x k))) (s l)
    le r (mulUp eps (maximumOver fun l => divDown (S l) (s l)))

/-- The orders from `i` while `fuel` lasts: the first `i ≥ 1` whose row sums are at most `eps`
times the sums `S` of the orders before it (and, with `tight`, whose remainder is at that level or
which is at least 60) stops, with those orders (in their order). -/
@[step_of LinearSys.verifyInputSolutionFloat]
def LinearSys.step_verifyInputSearchFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋)
    (u₀ : Interval (Mat 𝕋 n 1)) (M : Interval (Mat 𝕋 n m)) (tight : Bool) :
    ℕ → ℕ → List (Interval (Mat 𝕋 n 1) × Interval (Mat 𝕋 n m)) → Vec 𝕋 n →
      Option (ℕ × List (Interval (Mat 𝕋 n 1) × Interval (Mat 𝕋 n m)))
  | 0, _, _, _ => none
  | fuel + 1, i, acc, S =>
    let eps : 𝕋 := Nat.iterate half 52 one                                       -- eps = 2^-52
    let o := LinearSys.step_verifyInputOrderFloat A Δt u₀ M i
    let a := (Interval.point fun l => LinearSys.step_verifyInputRowSumFloat o l).materialise.sup
    if decide (1 ≤ i) && ((List.finRange n).all fun l => le (a l) (mulUp eps (S l))) &&
        (!tight || Nat.ble 60 i ||
          LinearSys.step_verifyInputRemainderOkFloat A s Δt u₀ M i S eps) then
      some (i, acc.reverse)
    else LinearSys.step_verifyInputSearchFloat A s Δt u₀ M tight fuel (i + 1) (o :: acc)
      (Interval.point fun l => addUp (S l) (a l)).materialise.sup


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The orders `i < η` and the remainder past them: the constant input's box `Σᵢ [Pᵢ u₀]` widened
by `Δt W |u₀|`, the boxes `[Pᵢ M]`, their sum, and `Δt W Σ_c |M_c|`. -/
def LinearSys.verifyInputSolutionFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋)
    (u₀ : Interval (Mat 𝕋 n 1)) (M : Interval (Mat 𝕋 n m)) (tight : Bool := false) :
    Option (LinearSys.VerifyInputSolution 𝕋 n m) := do
  let (η, O) ← LinearSys.step_verifyInputSearchFloat A s Δt u₀ M tight 75 0 [] fun _ => zero
  let W ← MatExp.scaledRemainderFloat A s Δt (η - 1)                          -- E(Δt, η-1)
  let mu := fun k => u₀.magnitudeMat k 0                                       -- |u₀|
  let mM := fun k => sumUp fun c => M.magnitudeMat k c                         -- Σ_c |M_c|
  let ρu := (Interval.point fun l =>                                          -- Δt W |u₀|
    mulUp Δt (sumUp fun k => mulUp (W l k) (mu k))).materialise.sup
  let ρ := (Interval.point fun l =>                                           -- Δt W Σ_c |M_c|
    mulUp Δt (sumUp fun k => mulUp (W l k) (mM k))).materialise.sup
  let w : Interval (Mat 𝕋 n 1) :=                                              -- Σᵢ [Pᵢ u₀] ± ρu
    ⟨fun l c => subDown (O.foldl (fun acc o => addDown acc (o.1.inf l c)) zero) (ρu l),
      fun l c => addUp (O.foldl (fun acc o => addUp acc (o.1.sup l c)) zero) (ρu l)⟩
  let Vs : Interval (Mat 𝕋 n m) :=                                             -- Σᵢ [Pᵢ M]
    ⟨fun l c => O.foldl (fun acc o => addDown acc (o.2.inf l c)) zero,
      fun l c => O.foldl (fun acc o => addUp acc (o.2.sup l c)) zero⟩
  pure ⟨w.materialiseMat, O.map Prod.snd, Vs.materialiseMat, ρ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
