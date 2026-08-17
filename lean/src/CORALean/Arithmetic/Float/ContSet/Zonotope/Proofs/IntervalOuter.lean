import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.MemGeneratorError

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

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

theorem interval_outer (Z : Zonotope F n h) : Z.construct ⊆ Z.interval.construct := by
  rintro _ ⟨z, ⟨β, hβ, hz⟩, e, he, rfl⟩ i
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

end CORALean.Arithmetic.Float.Zonotope.Proofs
