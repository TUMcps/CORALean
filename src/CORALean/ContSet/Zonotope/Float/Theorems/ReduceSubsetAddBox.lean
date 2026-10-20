module

public import CORALean.ContSet.Zonotope.Float.Operations.Reduce
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceBySubsetAddBox

@[expose] public section

/-!
# `reduce` reaches no further than its operand plus `reduceGirardBox`

The reverse of `reduce_outer`, and `Real`'s own `reduce_subset_add_box`
argument, unchanged: Girard's rule is the whole of the choice, so
`reduceBy_subset_add_box` at the partition it picks closes the case something
is dropped, and the degenerate `0` zonotope `reduceGirardBox` reduces to closes
the case nothing is — `0` lying in both its nominal set, at every coefficient
`0`, and its `0` error box.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reduction is contained in the zonotope plus the Girard box
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The degenerate `0` zonotope `reduceGirardBox` reduces to when nothing is
dropped: `n` generators, all `0`, and a `0` error box. -/
def Zonotope.aux_zeroZonotope : Zonotope (Vec 𝕋 n) :=
  ⟨n, fun _ => zero, fun _ _ => zero, ⟨fun _ => zero, fun _ => zero⟩⟩

/-- `0` lies in it: its nominal set at coefficients all `0`, plus its `0`
error box. -/
theorem Zonotope.aux_zero_mem_zeroZonotope : -- --- CONCL ---
    (0 : Vec ℝ n) ∈ (Zonotope.aux_zeroZonotope (𝕋 := 𝕋) (n := n)).construct := by -- --- PROOF ---
  have hnom : (0 : Vec ℝ n) ∈ nominalSet (Zonotope.aux_zeroZonotope (𝕋 := 𝕋) (n := n)) :=
    Zonotope.mem_nominalSet_iff.mpr ⟨0, fun _ => by norm_num, fun i => by
      show (0 : Vec ℝ n) i = toReal (zero : 𝕋) + ∑ _j : Fin n, toReal (zero : 𝕋) * (0 : ℝ)
      simp [toReal_zero]⟩
  have herr : (0 : Vec ℝ n) ∈
      (⟨fun _ => (zero : 𝕋), fun _ => (zero : 𝕋)⟩ : Interval (Vec 𝕋 n)).construct := fun i =>
    ⟨by show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i
        rw [toReal_zero]; exact le_refl 0,
     by show (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
        rw [toReal_zero]; exact le_refl 0⟩
  rw [show (0 : Vec ℝ n) = (0 : Vec ℝ n) + (0 : Vec ℝ n) from (add_zero 0).symm]
  exact Set.add_mem_add hnom herr


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reduce` reaches no further than `Z.construct` widened by
`reduceGirardBox` — the reverse of `reduce_outer`, and what a float run's own
accumulated error needs. -/
theorem Zonotope.reduce_subset_add_box (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : -- --- CONCL ---
    (Z.reduce o).construct ⊆
      Z.construct + (Zonotope.reduceGirardBox Z o).construct := by -- --- PROOF ---
  unfold Zonotope.reduce Zonotope.reduceGirard Zonotope.reduceGirardBox
  split_ifs with hlt
  · exact Z.reduceBy_subset_add_box _
  · intro x hx
    have h := Set.add_mem_add hx (Zonotope.aux_zero_mem_zeroZonotope (𝕋 := 𝕋) (n := n))
    rwa [add_zero] at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
