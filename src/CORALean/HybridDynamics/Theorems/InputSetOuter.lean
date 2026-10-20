module

public import CORALean.HybridDynamics.Operations.InputSet

@[expose] public section

/-!
# `Location.inputSet` holds every combined input

For every input `u ∈ U` and disturbance `w ∈ W` of a location, the combined input `B u + c + E w`
of its canonical form lies in `inputSet`: `B u` in the product `B U`, `c` in the point, `E w` in
`E W`, each by its operation's guarantee. So `IsTrajectory.linearSys` can name `inputSet` for every
stay.

## Inputs
* `ℓ` – location
* `u` – input value
* `w` – disturbance value

## Hypotheses
* `hu` – input lies in the input set
* `hw` – disturbance lies in the disturbance set

## Conclusion
* combined input lies in the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.inputSet_outer (ℓ : Location S G L 𝕋 n) {u : Vec ℝ ℓ.dynamics.m}
    {w : Vec ℝ ℓ.dynamics.r} (hu : u ∈ construct ℓ.U) (hw : w ∈ construct ℓ.W) : -- --- CONCL ---
    toRealMat ℓ.dynamics.B *ᵥ u + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w ∈
      construct ℓ.inputSet := by -- --- PROOF ---
  -- a real matrix is the singleton of itself, so `mtimes_outer` puts `M v` in `M V`
  have hM : ∀ {d : ℕ} (M : Mat ℝ n d) (V : S d) (v : Vec ℝ d), v ∈ construct V →
      M *ᵥ v ∈ construct (Mtimes.mtimes (𝕄 := Mat ℝ) M V) := fun M V v hv =>
    Mtimes.mtimes_outer (𝕄 := Mat ℝ) M V
      (Set.mem_biUnion (by simp [construct]) (Set.mem_image_of_mem _ hv))
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add (hM _ _ _ hu) (OfPoint.mem_ofPoint _))) (hM _ _ _ hw))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
