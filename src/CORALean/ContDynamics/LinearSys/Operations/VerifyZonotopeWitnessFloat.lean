module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifySpecSet
public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.BalanceScalesFloat
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyZonotopeWitnessFloat`, a falsification checked on one trajectory

CORA's `priv_verifyRA_zonotope` falsifies through an inner approximation, its distance to an
unsafe set snapped by a tolerance. Here a falsification is a witness: an initial point
`c + G b` and a constant input `u_c + G_U β` (`|b|, |β| ≤ 1`), and a time `t`. Its state
`e^{tA} x₀ + (∫₀^t e^{σA} dσ) B u` is enclosed in a box (`MatExp.expBallFloat`, the input's
solution), mapped by `C`; the witness holds when the whole box violates the specification: lies
in the unsafe set, or past a row of the safe set. One enclosure per candidate, off the hot path.

## Inputs
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `S` – float safe or unsafe set
* `t` – float time
* `b` – float coefficients of the initial point
* `β` – float coefficients of the input

## Output
* whether the witness violates `S` at `t`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k p q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `a'y` over the box `[lo, hi]`, rounded up: each term at the better end. -/
@[step_of LinearSys.verifyZonotopeWitnessFloat]
def LinearSys.step_verifyWitnessDotUpFloat (a lo hi : Vec 𝕋 q) : 𝕋 :=
  sumUp fun i => maximum (mulUp (a i) (lo i)) (mulUp (a i) (hi i))

/-- The box of `c + M v` for `v` a float point: `M v` rounded down and up. -/
@[step_of LinearSys.verifyZonotopeWitnessFloat]
def LinearSys.step_verifyWitnessPointFloat (c : Vec 𝕋 n) (M : Mat 𝕋 n m) (v : Vec 𝕋 m) :
    Interval (Mat 𝕋 n 1) :=
  ⟨fun i _ => addDown (c i) (dotDown (M i) v), fun i _ => addUp (c i) (dotUp (M i) v)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The witness `c + G b`, `u_c + G_U β` at `t`: its output's box against `S`, after the checks
`|b|, |β| ≤ 1`, `t > 0` and positive scales. -/
def LinearSys.verifyZonotopeWitnessFloat (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (S : LinearSys.VerifySpecSet 𝕋 q) (t : 𝕋) (b : Vec 𝕋 m) (β : Vec 𝕋 p) : Bool :=
  let s := MatExp.balanceScalesFloat A
  let X₀ := LinearSys.step_verifyWitnessPointFloat c G b                -- c + G b
  let U₀ := (Interval.matMul (Interval.point Bm)                         -- B (u_c + G_U β)
    (LinearSys.step_verifyWitnessPointFloat uc GU β)).materialiseMat
  let none₀ : Interval (Mat 𝕋 n 0) := Interval.point fun _ j => j.elim0
  let ok := (List.finRange m).all (fun j => le (absolute (b j)) one) &&
    (List.finRange p).all (fun j => le (absolute (β j)) one) && ltStrict zero t &&
    (List.finRange n).all fun i => ltStrict zero (s i)
  match MatExp.expBallFloat A s t, LinearSys.verifyInputSolutionFloat A s t U₀ none₀ with
  | some (D, r), some I =>
    let DX := (Interval.matMul (Interval.point D) X₀).materialiseMat     -- D x₀
    let ν := maximum zero (maximumOver fun i =>                          -- ≥ max |x₀ᵢ| / sᵢ
      divUp (maximum (absolute (X₀.inf i 0)) (absolute (X₀.sup i 0))) (s i))
    let e := mulUp r ν                                                   -- (e^{tA} − D) x₀
    let Xt : Interval (Mat 𝕋 n 1) :=                                     -- x(t)
      ⟨fun i _ => subDown (addDown (DX.inf i 0) (I.w.inf i 0)) (mulUp e (s i)),
        fun i _ => addUp (addUp (DX.sup i 0) (I.w.sup i 0)) (mulUp e (s i))⟩
    let Y := (Interval.matMul (Interval.point C) Xt).materialiseMat      -- C x(t)
    let up := fun a : Vec 𝕋 q =>
      LinearSys.step_verifyWitnessDotUpFloat a (fun i => Y.inf i 0) (fun i => Y.sup i 0)
    ok && if S.safe then S.rows.any fun ab => ltStrict ab.2 (neg (up (-ab.1)))
      else S.rows.all fun ab => le (up ab.1) ab.2
  | _, _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
