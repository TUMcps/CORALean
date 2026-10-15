module

public import CORALean.ContDynamics.LinearSys.Definitions.CanonicalClassicalTrajectory
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# A stay in a location is a run of its canonical form

`Location.Trajectory` runs the whole equation `ẋ = A x + B u + c + E w`;
`LinearSys.CanonicalClassicalTrajectory` runs `ẋ = A x + u'`, anchored at a set and with no
invariant. A stay is a run of the latter with the combined input `u' = B u + c + E w`, CORA's
`canonicalForm`, wherever the caller's set `U'` holds every value it takes — at `ℓ.inputSet`
(`B U ⊕ c ⊕ E W`, `memInputSet`) or its float counterpart. Naming a set the initial point lies in
and one the combined input lies in is all it takes to hand a stay to the whole of `LinearSys`
through `CanonicalClassicalTrajectory.trajectory`; the invariant is dropped — it only ever
tightens an enclosure, never justifies one.

The time domain is `Set.Icc 0 τ` on the location's own clock, which is the shape every bounded
statement in `LinearSys` asks for.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stay read as a run of the location's canonical form, starting in any set that holds its
initial point, its combined input `B u + c + E w` in any set that holds it. -/
theorem Location.Trajectory.linearSys {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ ℓ.dynamics.m} {w : ℝ → Vec ℝ ℓ.dynamics.r} (traj : ℓ.Trajectory τ x u w)
    {R₀ U' : S n} (h₀ : x 0 ∈ construct R₀)
    (hU' : ∀ t ∈ Set.Icc 0 τ, toRealMat ℓ.dynamics.B *ᵥ u t + toRealVec ℓ.dynamics.c +
      toRealMat ℓ.dynamics.E *ᵥ w t ∈ construct U') :
    ℓ.dynamics.CanonicalClassicalTrajectory (Set.Icc 0 τ) R₀ U' x
      (fun t => toRealMat ℓ.dynamics.B *ᵥ u t + toRealVec ℓ.dynamics.c +
        toRealMat ℓ.dynamics.E *ᵥ w t) where
  init := h₀
  input := hU'
  -- the same sum, bracketed as `A x + (B u + c + E w)`
  flow t ht := by
    have h := traj.flow t ht
    simp only [add_assoc] at h ⊢
    exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
