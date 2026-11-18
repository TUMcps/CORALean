module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyKrylovDirection
public import CORALean.ContDynamics.LinearSys.Operations.VerifyKrylovBoundsFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyKrylovWindowsFloat

@[expose] public section

/-!
# `LinearSys.verifyKrylovPassFloat`, one pass of CORA.cpp's Krylov verification, made sound

CORA.cpp's `aux_pass` (`priv_verify_ra_krylov.cpp`) for `ẋ = Ax + u`, `u(t) ∈ ⟨u_c, G_U⟩`, from
`X₀ = ⟨c, G⟩`: every direction gets its windows on the grid `Δt₀`
(`LinearSys.verifyKrylovWindowsFloat`, its plan and certificate CORA.cpp's tuning) and its bounds
on the `N` steps of `Δt = Δt₀ / 2^h` (`LinearSys.verifyKrylovBoundsFloat`); the pass holds if on
every step every group has a direction whose bound stays below its limit (strictly, for an unsafe
set's row).
CORA.cpp's loop that halves the step, and its `hopeless` stop, are tuning and are not formalized:
this is one pass for a given `h`. A pass that does not hold is undecided, never a falsification.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold of Arnoldi
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `uc` – float center of the input set, in the state space
* `GU` – float generators of the input set, in the state space
* `dirs` – the directions
* `cert` – Lyapunov certificate `(P, L, a)` of `A'`, if any
* `groups` – the number of groups
* `Δt₀` – float step size of the windows
* `h` – halvings of the step size
* `N` – number of steps

## Output
* `true` if every group holds on every step
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m p' : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds of every direction, then every group on every step. -/
def LinearSys.verifyKrylovPassFloat (p q : ℕ) (εb : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p')
    (dirs : List (LinearSys.VerifyKrylovDirection 𝕋 n))
    (cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋)) (groups : ℕ) (Δt₀ : 𝕋) (h N : ℕ) : Bool :=
  let Δt := half^[h] Δt₀                                                  -- Δt₀ / 2^h
  match dirs.mapM fun d => (LinearSys.verifyKrylovWindowsFloat p q εb A d.w Δt₀ d.plan cert).bind
      fun wins => LinearSys.verifyKrylovBoundsFloat c G uc GU d.w wins (2 ^ h) Δt N with
  | none => false
  | some Bs =>
    (List.range N).all fun j => (List.range groups).all fun g =>
      (dirs.zip Bs).any fun dB => dB.1.group == g &&
        match dB.2[j]? with
        | some b => if dB.1.strict then ltStrict b dB.1.limit else le b dB.1.limit
        | none => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
