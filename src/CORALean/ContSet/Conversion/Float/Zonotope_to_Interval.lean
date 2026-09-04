import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

/-!
# A zonotope as a box, over a floating-point scalar

The centre give or take the generators' total reach, each end rounded away from
the zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.interval (Z : Zonotope 𝕋 n) : Interval 𝕋 n where
  inf := fun i => addDown (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)
  sup := fun i => addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i)

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
  -- each face on its own, the two roundings going opposite ways
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
