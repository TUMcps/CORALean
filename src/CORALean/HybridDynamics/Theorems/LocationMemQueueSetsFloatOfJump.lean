module

public import CORALean.HybridDynamics.Operations.LocationQueueSetsFloat
public import CORALean.HybridDynamics.Theorems.LocationGuardOrientFloatSound
public import CORALean.HybridDynamics.Theorems.LocationMemCheckFlowFloatOfJump

@[expose] public section

/-!
# The set holding the end state of a stay on the guard is among the sets `queueSetsFloat` keeps

A stay of positive length ends on the guard hyperplane `nv·z = γ` in the `k`-th reach set, `k` in
the group. If `checkFlow` is on and the invariant's side is certified, the set is kept by
`Location.mem_checkFlowFloat_of_jump` (the oriented normal is out of the invariant, so the stay
comes from `c·y ≤ d`); otherwise every set of the group is kept.

## Inputs
* `ℓ` – location
* `chk` – whether `checkFlow` is on
* `nv` – normal of the guard hyperplane
* `γ` – offset of the guard hyperplane
* `idxs` – set indices of the group
* `Rs` – sets of the stay
* `k` – set index of the end state
* `R` – the set of the end state
* `τ` – length of the stay
* `x` – state
* `u` – input of the stay, in `U` at every time
* `w` – disturbance of the stay, in `W` at every time

## Hypotheses
* `hk` – the set index is in the group
* `hR` – the set is the `k`-th
* `traj` – the stay
* `hτ` – the stay has positive length (needed when `checkFlow` is on)
* `hxR` – the end state lies in the set
* `hxg` – the end state is on the hyperplane

## Conclusion
* the set is among the kept sets
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.mem_queueSetsFloat_of_jump
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (chk : Bool) (nv : Vec 𝕋 n)
    (γ : 𝕋) {idxs : List ℕ} (Rs : List (Zonotope (Vec 𝕋 n))) {k : ℕ} (hk : k ∈ idxs)
    {R : Zonotope (Vec 𝕋 n)} (hR : Rs[k]? = some R) {τ : ℝ} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ ℓ.dynamics.m} {w : ℝ → Vec ℝ ℓ.dynamics.r} (traj : ℓ.IsTrajectory τ x u w)
    (hτ : chk = true → 0 < τ) (hxR : x τ ∈ R.toSet)
    (hxg : x τ ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    R ∈ ℓ.queueSetsFloat chk nv γ idxs Rs := by -- --- PROOF ---
  have hmem : R ∈ idxs.filterMap fun j => Rs[j]? := List.mem_filterMap.mpr ⟨k, hk, hR⟩
  unfold Location.queueSetsFloat
  split
  · rename_i c d hcd
    obtain ⟨hinv, hz⟩ := ℓ.guardOrientFloat?_sound nv γ _ (Option.mem_def.mpr hcd)
    exact ℓ.mem_checkFlowFloat_of_jump c d _ hmem traj (hτ rfl) hinv hxR (hz _ hxg)
  · exact hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
