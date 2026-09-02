import CORALean.ContSet.Zonotope.Float.Operations.Interval
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

/-!
# `Zonotope.interval` contains the zonotope

The generators reach at most `radius` either way, and the box adds its own
bounds. Both roundings go outward, and an `Interval` has no box to charge, so
they widen the bounds themselves.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem Zonotope.interval_outer (Z : Zonotope 𝕋 n) : Z.construct ⊆ Z.interval.construct := by
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hzmem
  have hgen := abs_sum_le_radius (d := Z.G) (Δ := fun i j => toReal (Z.G i j))
    (fun _ _ => le_refl _) hβ i
  have hlo : toReal (Z.E.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.E.sup i) := (he i).2
  have hzi : z i = toReal (Z.c i) + ∑ j, toReal (Z.G i j) * β j := hz i
  constructor
  · have h1 := addDown_le_add (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)
    have h2 := subDown_le_sub (Z.c i) (radius Z.G i)
    have h3 := neg_le_of_abs_le hgen
    show toReal (addDown (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)) ≤ z i + e i
    rw [hzi]
    linarith
  · have h1 := add_le_addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i)
    have h2 := add_le_addUp (Z.c i) (radius Z.G i)
    have h3 := le_of_abs_le hgen
    show z i + e i ≤ toReal (addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i))
    rw [hzi]
    linarith

end CORALean.Float
