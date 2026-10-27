module

public import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `isCanonicalForm` at float matrices

CORA's `isCanonicalForm` [1] as a Boolean on float entries: `m = n`, `s = q`, `c`, `k`, `E`, `D`
zero and `B = I`, each entry tested by `LinearSys.step_entryIsFloat`. Soundness is
`LinearSys.isCanonicalFormFloat_sound`, one-sided as the test is.

## Inputs
* `sys` – linear system with float coefficients

## Output
* whether the system is in canonical form

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋]

/-- The entry equals `a`, as far as `le` can tell: `a ≤ x` and `x ≤ a`. -/
@[step_of LinearSys.isCanonicalFormFloat]
def LinearSys.step_entryIsFloat (a x : 𝕋) : Bool := le a x && le x a

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `isCanonicalForm`, on float coefficients. -/
def LinearSys.isCanonicalFormFloat (sys : LinearSys 𝕋 n) : Bool :=
  (sys.m == n) && (sys.s == sys.q) &&
    (List.finRange n).all (fun i => LinearSys.step_entryIsFloat zero (sys.c i)) &&
    (List.finRange sys.q).all (fun i => LinearSys.step_entryIsFloat zero (sys.k i)) &&
    (List.finRange n).all (fun i => (List.finRange sys.r).all fun j =>
      LinearSys.step_entryIsFloat zero (sys.E i j)) &&
    (List.finRange sys.q).all (fun i => (List.finRange sys.m).all fun j =>
      LinearSys.step_entryIsFloat zero (sys.D i j)) &&
    (List.finRange n).all (fun i => (List.finRange sys.m).all fun j =>
      LinearSys.step_entryIsFloat (if (i : ℕ) = (j : ℕ) then one else zero) (sys.B i j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
