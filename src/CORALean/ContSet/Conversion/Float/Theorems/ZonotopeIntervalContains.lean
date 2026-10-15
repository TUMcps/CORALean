module

public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Data.Matrix.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A zonotope as a box, over a floating-point scalar

The center give or take the generators' total reach, each end rounded away from
the zonotope.

`Zonotope.matInterval` is the same entry by entry at `Mat`, CORA's
`intervalMatrix(matZonotope)`: what the matrix-zonotope product needs of a factor's
error terms, and what bounds a norm.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.interval_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.interval.construct := by -- --- PROOF ---
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hzmem
  have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
    (fun _ _ => le_refl _) hβ i
  have hlo : toReal (Z.I_error.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.I_error.sup i) := (he i).2
  have hzi : z i = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * β j := hz i
  -- each face on its own, the two roundings going opposite ways
  constructor
  · have h1 := addDown_le_add (subDown (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.inf i)
    have h2 := subDown_le_sub (Z.c i) (radius (fun i j => Z.G j i) i)
    have h3 := neg_le_of_abs_le hgen
    show toReal (addDown (subDown (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.inf i)) ≤ z i
        + e i
    rw [hzi]
    linarith
  · have h1 := add_le_addUp (addUp (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.sup i)
    have h2 := add_le_addUp (Z.c i) (radius (fun i j => Z.G j i) i)
    have h3 := le_of_abs_le hgen
    show z i + e i ≤ toReal
        (addUp (addUp (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.sup i))
    rw [hzi]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
