module

public import CORALean.HybridDynamics.Theorems.CheckFlowFloatDropped
public import CORALean.HybridDynamics.Theorems.LocationIsTrajectoryNotStrictlyInward

@[expose] public section

/-!
# A set holding the end state of a stay on the guard is kept by `Location.checkFlowFloat`

A stay of positive length inside `{y | c·y ≤ d}` that ends in a reach set `R` on the hyperplane
`{y | c·y = d}`: if `R` were dropped, the flow along `c` at the end state would be below one
`b < 0` for every input and disturbance (`Location.checkFlowFloat_dropped`, the end state being its
own projection), and the stay would have come from outside the halfspace
(`Location.IsTrajectory.not_strictly_inward`). So `R` is kept. With a tangential end state the
test of CORA, which drops at `sup ≤ 0`, loses the jump; `checkFlowFloat` drops at `sup < 0` only.

## Inputs
* `ℓ` – location
* `c` – normal of the guard, out of the invariant
* `d` – guard offset
* `Rs` – reach sets
* `R` – the reach set of the end state
* `τ` – length of the stay
* `x` – state
* `u` – input of the stay, in `U` at every time
* `w` – disturbance of the stay, in `W` at every time

## Hypotheses
* `hR` – `R` is among the reach sets
* `traj` – the stay
* `hτ` – the stay has positive length
* `hinv` – the invariant lies in `c·y ≤ d`
* `hxR` – the end state lies in `R`
* `hxd` – the end state is on the hyperplane

## Conclusion
* `R` is kept
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSetLike

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSetLike (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set the end state of a stay on the guard lies in is not dropped. -/
theorem Location.mem_checkFlowFloat_of_jump
    (ℓ : Location 𝒵[𝕋] G L 𝕋 n) (c : Vec 𝕋 n) (d : 𝕋) (Rs : List (Zonotope (Vec 𝕋 n)))
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ Rs) {τ : ℝ} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ ℓ.dynamics.m} {w : ℝ → Vec ℝ ℓ.dynamics.r} (traj : ℓ.IsTrajectory τ x u w)
    (hτ : 0 < τ) (hinv : ∀ y ∈ toSet ℓ.inv, toRealVec c ⬝ᵥ y ≤ toReal d)
    (hxR : x τ ∈ R.toSet) (hxd : toRealVec c ⬝ᵥ x τ = toReal d) : -- --- CONCL ---
    R ∈ ℓ.checkFlowFloat c d Rs := by -- --- PROOF ---
  by_contra hdrop
  obtain ⟨b, hb, hbd⟩ := ℓ.checkFlowFloat_dropped c d Rs hR hdrop hxR
  refine traj.not_strictly_inward hτ (toRealVec c) (toReal d) hinv hxd hb fun s hs => ?_
  have := hbd (traj.input s hs) (traj.dist s hs)
  rwa [hxd, sub_self, zero_smul, sub_zero] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
