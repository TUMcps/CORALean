module

public import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm

@[expose] public section

/-!
# The system `canonicalForm` returns is in canonical form [1]

`(A, I, 0, C, 0, 0, 0, I)`: `B = I`, `c = k = 0`, `E = 0`, `D = 0` and `F = I`, `n` inputs,
`q` noises, whatever system it was handed.

## Inputs
* `sys` – linear system
* `U` – input set
* `uVec` – input offset
* `W` – disturbance set
* `V` – noise set
* `vVec` – noise offset

## Hypotheses
* none

## Conclusion
* the returned system is in canonical form

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.isCanonicalForm_canonical (sys : LinearSys ℝ n) (U : S sys.m)
    (uVec : Vec ℝ sys.m) (W : S sys.r) (V : S sys.s) (vVec : Vec ℝ sys.s) : -- --- CONCL ---
    (sys.canonicalForm U uVec W V vVec).1.IsCanonicalForm := by -- --- PROOF ---
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun i j => ?_⟩
  -- the identity matrix against the value test
  show (1 : Mat ℝ n n) i j = _
  rw [Matrix.one_apply]
  simp only [Fin.ext_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
