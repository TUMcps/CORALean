module

public import CORALean.ContSet.ConZonotope.Float.Operations.Rescale
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemRescaleColsNominal
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

@[expose] public section

/-!
# The float `rescale` encloses the constrained zonotope

When every feasible coefficient vector lies in `[ξL, ξU]` (over ℝ: the box contains
`B∞(A, b)`), each one is `ξm + diag(ξr) δ` with `|δ| ≤ 1`, since the float radius reaches both
ends from the float midpoint. The point at `ξ` is then the rescaled nominal point at `δ` plus
the old error, the center's rounding and the generators' rounding against `δ`, which is what
the new error box holds; and `δ` meets the rescaled rows (`HPolytope.mem_rescaleCols_nominal`).
Outer: the exact layer's `rescale_exact` is an equality, this is not.

## Inputs
* `cZ` – float constrained zonotope
* `ξL` – lower coefficient bounds
* `ξU` – upper coefficient bounds

## Hypotheses
* `hB` – every feasible coefficient vector lies in the box

## Conclusion
* the set is contained in the rescaled set
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.rescale_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (ξL ξU : Vec 𝕋 cZ.h)
    (hB : ∀ ξ : Vec ℝ cZ.h, (∀ j, |ξ j| ≤ 1) → ξ ∈ cZ.P.nominal.construct →
      ∀ j, toReal (ξL j) ≤ ξ j ∧ ξ j ≤ toReal (ξU j)) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.rescale ξL ξU).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy', e, he, rfl⟩
  obtain ⟨ξ, hξ, hP, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  set ξm : Vec 𝕋 cZ.h := fun j => half (addDown (ξU j) (ξL j)) with hξm
  set ξr : Vec 𝕋 cZ.h := fun j => maximum (subUp (ξU j) (ξm j)) (subUp (ξm j) (ξL j)) with hξr
  -- the radius reaches both ends of the box from the midpoint
  have hdev : ∀ j, |ξ j - toReal (ξm j)| ≤ toReal (ξr j) := by
    intro j
    have h1 := sub_le_subUp (ξU j) (ξm j)
    have h2 := sub_le_subUp (ξm j) (ξL j)
    have h3 : toReal (ξr j) = max (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j))) :=
      toReal_maximum _ _
    have h4 := le_max_left (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j)))
    have h5 := le_max_right (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j)))
    have hb := hB ξ hξ hP j
    rw [abs_le]
    constructor <;> linarith
  -- the rescaled coefficients, `0` where the box is a point
  set δ : Vec ℝ cZ.h := fun j =>
    if toReal (ξr j) = 0 then 0 else (ξ j - toReal (ξm j)) / toReal (ξr j) with hδdef
  have hδ : ∀ j, |δ j| ≤ 1 := by
    intro j
    simp only [hδdef]
    split_ifs with h0
    · simp
    · have hpos : 0 < toReal (ξr j) :=
        lt_of_le_of_ne (le_trans (abs_nonneg _) (hdev j)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hdev j
  -- and they map back onto the old ones
  have hξδ : ∀ j, ξ j = toReal (ξm j) + toReal (ξr j) * δ j := by
    intro j
    simp only [hδdef]
    split_ifs with h0
    · have := hdev j
      rw [h0] at this
      have : ξ j - toReal (ξm j) = 0 := abs_nonpos_iff.mp this
      rw [h0]; linarith
    · field_simp
      ring
  -- the generators' rounding against `δ`, entrywise
  have hgen : ∀ i j, |toReal (cZ.G j i) * toReal (ξr j) - toReal (mulDown (cZ.G j i) (ξr j))|
      ≤ toReal (subUp (mulUp (cZ.G j i) (ξr j)) (mulDown (cZ.G j i) (ξr j))) :=
    fun i j => mulDown_gap _ _
  -- the stored center's rounding
  have hcen : ∀ i, toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
        ≤ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
      ∧ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
        ≤ toReal (addUp (cZ.c i) (dotUp (fun j => cZ.G j i) ξm)) := by
    intro i
    have h1 := dotDown_le (fun j => cZ.G j i) ξm
    have h2 := le_dotUp (fun j => cZ.G j i) ξm
    have h3 := addDown_le_add (cZ.c i) (dotDown (fun j => cZ.G j i) ξm)
    have h4 := add_le_addUp (cZ.c i) (dotUp (fun j => cZ.G j i) ξm)
    constructor <;> linarith
  refine ⟨fun i => toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
      + ∑ j, toReal (mulDown (cZ.G j i) (ξr j)) * δ j,
    ConZonotope.mem_nominalSet_iff.mpr
      ⟨δ, hδ, HPolytope.mem_rescaleCols_nominal cZ.P ξm ξr hδ hξδ hP, fun _ => rfl⟩,
    _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e, he, _,
      Interval.sub_mem_residual
        (stored := fun i => addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm)) hcen,
      rfl⟩, _, Zonotope.mem_generatorError hgen hδ, rfl⟩, ?_⟩
  · -- the point: the rescaled one plus the old error and the two roundings
    funext i
    have hs := sum_mul_affine_split (fun j => cZ.G j i) ξm ξr δ ξ hξδ
    have hyi := hy i
    show (toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
        + ∑ j, toReal (mulDown (cZ.G j i) (ξr j)) * δ j)
      + ((e i + (toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
          - toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))))
        + ∑ j, (toReal (cZ.G j i) * toReal (ξr j) - toReal (mulDown (cZ.G j i) (ξr j))) * δ j)
      = y i + e i
    rw [hyi, hs]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
