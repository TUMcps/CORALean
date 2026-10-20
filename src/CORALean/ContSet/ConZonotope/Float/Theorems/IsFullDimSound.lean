module

public import CORALean.ContSet.ConZonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemInterior
public import CORALean.ContSet.ConZonotope.Float.Theorems.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `ConZonotope.isFullDim` proves an interior point

A passed `interiorCert` puts the open box of radius `B` around `y₀ = c + G β₀` in the nominal set
(`ConZonotope.mem_interior`), so `y₀` is an interior point of it; moving by the error box's lower
corner, a member of the nonempty box, carries that to the set itself. This certifies the real
property `ContSet.IsFullDim`, not CORA's rank test (`rank(G null(A)) = n`), which is necessary only.

## Inputs
* `cZ` – float constrained zonotope
* `H` – right inverse of the generator matrix
* `β₀` – coefficient point

## Hypotheses
* `h` – the test answers true

## Conclusion
* the set has an interior point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isFullDim_sound {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cZ.h n}
    {β₀ : Vec 𝕋 cZ.h} (h : cZ.isFullDim H β₀ = true) : -- --- CONCL ---
    (interior cZ.construct).Nonempty := by -- --- PROOF ---
  simp only [ConZonotope.isFullDim, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hc, hE⟩ := h
  have hball : Zonotope.ballCert (fun i j => cZ.G j i) H (Zonotope.ballB H (cZ.interiorMargin β₀))
      (cZ.interiorMargin β₀) = true := by
    simp only [ConZonotope.interiorCert, Bool.and_eq_true] at hc
    exact hc.2
  obtain ⟨hB, -⟩ := Zonotope.ballCert_reach hball
  have hx := ConZonotope.mem_interior hc
    (fun i => toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)) fun i => by simpa using hB
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx (ConZonotope.corner_mem hE))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
