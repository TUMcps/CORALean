module

public import CORALean.ContDynamics.LinParamSysDT.Operations.InputSet

@[expose] public section

/-!
# Every run is a run of the canonical form

A run of `x(k+1) = A(k) x(k) + B(k) u(k) + c` is a run of the canonical form
`x(k+1) = A(k) x(k) + u'(k)` with the combined input `u' = B u + c`, wherever `U'` holds every
value it takes: the right-hand side is the same sum, bracketed differently. So whatever is proved
of `CanonicalTrajectory` at an input set `U' ⊇ B U ⊕ c` holds of every run, as for
`LinParamSys.Trajectory.canonical`. `mem_inputSet` is the `U'` CORA's `V = B*U + c` gives.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combined input `B u + c` drives the canonical form along the same state. -/
theorem LinParamSysDT.Trajectory.canonical {sys : LinParamSysDT 𝕄 n} {R₀ : S n} {U : S sys.m}
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ sys.m} {A : ℕ → Mat ℝ n n} {B : ℕ → Mat ℝ n sys.m}
    (traj : sys.Trajectory R₀ U x u A B) {U' : S n}
    (hU' : ∀ k, B k *ᵥ u k + sys.c ∈ construct U') :
    sys.CanonicalTrajectory R₀ U' x (fun k => B k *ᵥ u k + sys.c) where
  init := traj.init
  input := hU'
  -- the same sum, bracketed as `A x + (B u + c)`
  step k := ⟨A k, traj.param k, by rw [traj.step k, add_assoc]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
