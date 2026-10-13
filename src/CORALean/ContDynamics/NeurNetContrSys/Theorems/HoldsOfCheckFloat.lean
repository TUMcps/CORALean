module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A passed check on the float loop's reachable set holds along it

`NeurNetContrSys.holds_of_check` at `reachFloat`: a `true` from `Specification.check` on the
zonotope `reachFloat` computes, found by evaluation, is the specification on the exact state at
the period boundary, since `reachFloat_outer` puts that state in the zonotope.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.holds_of_checkFloat [Contains ContSet (Zonotope (Vec 𝕋 n))]
    [IsDisjoint ContSet (Zonotope (Vec 𝕋 n))]
    (sys : NeurNetContrSys 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n)
    (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    (hη : sys.plant.OrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π) {x : ℝ → Vec ℝ n}
    (traj : sys.Trajectory π ((N : ℝ) * toReal Δt) H R₀ x)
    (spec : Specification ContSet) (i : ℕ) (hi : i ≤ H) :
    spec.check (sys.reachFloat ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) →
      (spec.Holds {x ((i : ℝ) * ((N : ℝ) * toReal Δt))}) :=
  fun h => spec.holds_of_outer (Set.singleton_subset_iff.2
    (sys.reachFloat_outer o η N ho hΔt hη hπ traj i hi)) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
