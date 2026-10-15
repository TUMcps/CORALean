module

public import CORALean.ContDynamics.LinParamSys.LinParamSys

@[expose] public section

/-!
# The exact set `Reach (LinParamSys ℐ)` is asked to enclose

Every state a `'constParam'` run on the horizon `[0, tFinal]` is at, at some time of it: one
`A` of `sys.A` and one `B` of `sys.B` fixed over the whole run, the initial state in a bare set
`X`, the input `u t` in `U` in input coordinates, and the offset `sys.c` — `IsConstTrajectory`
at the representation `Set` itself. The windows `reachUnion` covers the horizon with, and the
`B U ⊕ c` it computes, are how it encloses this set, not part of it.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a constant-parameter run on `[0, tFinal]` from a bare initial set `X`, under
inputs in `U` (input coordinates), is at, at some time of that horizon. -/
def LinParamSys.reachUnionExact (sys : LinParamSys 𝕄 n) (tFinal : ℝ) (X : Set (Vec ℝ n))
    (U : Set (Vec ℝ sys.m)) : Set (Vec ℝ n) :=
  {y | ∃ (A : Mat ℝ n n) (B : Mat ℝ n sys.m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ sys.m),
    sys.IsConstTrajectory (S := 𝒮) (Set.Icc 0 tFinal) X U x u A B ∧
      ∃ t ∈ Set.Icc (0 : ℝ) tFinal, x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
