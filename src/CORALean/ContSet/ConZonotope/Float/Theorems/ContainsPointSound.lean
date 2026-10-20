module

public import CORALean.ContSet.ConZonotope.Float.Operations.ContainsPoint
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoxSubset
public import CORALean.ContSet.ConZonotope.Float.Theorems.CenterBetween
public import CORALean.ContSet.ConZonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.DeviationBound

@[expose] public section

/-!
# A `true` from `ConZonotope.containsPoint` proves membership

A point within `B` of `y₀ = c + G β₀` after the error box's lower corner is subtracted is in the
nominal set (`ConZonotope.box_subset`); adding the corner, a member of the nonempty box, gives
the point.

## Inputs
* `cZ` – float constrained zonotope
* `H` – right inverse of the generator matrix
* `β₀` – coefficient point
* `p` – point to test

## Hypotheses
* `h` – the test answers true

## Conclusion
* the point lies in the set
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

theorem ConZonotope.containsPoint_sound {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cZ.h n}
    {β₀ : Vec 𝕋 cZ.h} {p : Vec 𝕋 n} (h : cZ.containsPoint H β₀ p = true) : -- --- CONCL ---
    toRealVec p ∈ cZ.construct := by -- --- PROOF ---
  simp only [ConZonotope.containsPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hd⟩, hE⟩ := h
  have hdev := toReal_le_of_le hd
  have hx : (fun i => toReal (p i) - toReal (cZ.I_error.inf i)) ∈ nominalSet cZ :=
    ConZonotope.box_subset hc _ fun i =>
      le_trans (Zonotope.deviation_bound p cZ.I_error.inf (cZ.centerLo β₀) (cZ.centerHi β₀)
        (fun i => toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j))
        (fun i => (ConZonotope.center_between cZ β₀ i).1)
        (fun i => (ConZonotope.center_between cZ β₀ i).2) i) hdev
  have hsum : toRealVec p = (fun i => toReal (p i) - toReal (cZ.I_error.inf i))
      + fun i => toReal (cZ.I_error.inf i) := by
    funext i
    simp [toRealVec]
  rw [hsum]
  exact Set.add_mem_add hx (ConZonotope.corner_mem hE)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
