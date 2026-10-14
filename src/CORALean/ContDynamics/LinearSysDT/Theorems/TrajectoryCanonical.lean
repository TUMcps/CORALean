module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# Every run is a run of the canonical form

A run of `x(k+1) = A x(k) + B u(k) + c + E w(k)` is a run of the canonical form
`x(k+1) = A x(k) + u'(k)` with the combined input `u' = B u + c + E w`, wherever `U'` holds every
value it takes. So whatever is proved of `CanonicalTrajectory` at an input set
`U' ⊇ B U ⊕ c ⊕ E W` holds of every run of the full system. The output plays no part.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combined input `B u + c + E w` drives the canonical form along the same state. -/
theorem LinearSysDT.Trajectory.canonical {sys : LinearSysDT 𝕋 n} {X₀ : S n} {U : S sys.m}
    {W : S sys.r} {V : S sys.s} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ sys.m}
    {w : ℕ → Vec ℝ sys.r} {v : ℕ → Vec ℝ sys.s} {y : ℕ → Vec ℝ sys.q}
    (traj : sys.Trajectory X₀ U W V x u w v y) {U' : S n}
    (hU' : ∀ k, toRealMat sys.B *ᵥ u k + toRealVec sys.c + toRealMat sys.E *ᵥ w k ∈ construct U') :
    sys.CanonicalTrajectory X₀ U' x
      (fun k => toRealMat sys.B *ᵥ u k + toRealVec sys.c + toRealMat sys.E *ᵥ w k) where
  init := traj.init
  input := hU'
  -- the same sum, bracketed as `A x + (B u + c + E w)`
  step k := by
    rw [traj.step k]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
