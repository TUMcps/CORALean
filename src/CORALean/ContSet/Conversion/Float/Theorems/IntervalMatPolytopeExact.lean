module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_MatPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.VPolytope.Float.Theorems.UnvecExact

@[expose] public section

/-!
# `Interval.matPolytope` denotes the interval matrix

The corners of the stacked box have the stacked box as their hull, and stacking and unstacking are
exact, so the matrix polytope of the corners denotes the matrices of the box. The box is nonempty
entrywise for equality; the corners always contain the box.

## Inputs
* `I` – interval matrix

## Hypotheses
* `hI` – the stored bounds are ordered entrywise

## Conclusion
* the corners denote exactly the matrices of the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matPolytope_exact (I : Interval (Mat 𝕋 m n))
    (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) : -- --- CONCL ---
    InflatedContSet.construct I.matPolytope = I.construct := by -- --- PROOF ---
  -- the stacked bounds are ordered too
  have hv : ∀ k, toReal (I.vec.inf k) ≤ toReal (I.vec.sup k) := fun k => hI _ _
  -- unstack the exact corners of the stacked box
  have h1 := VPolytope.unvec_exact (Interval.vPolytope I.vec)
  have h2 : InflatedContSet.construct (Interval.vPolytope I.vec) = I.vec.construct :=
    Interval.vPolytope_exact I.vec hv
  rw [h2, Interval.vec_exact, Set.image_image] at h1
  rw [Interval.matPolytope]
  simpa using h1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
