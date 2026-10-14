import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsPointIff
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeConPolyZonoContains
import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConPolyZonoExact
import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact

/-!
# Cutting a non-convex set by a guard

What the interval right-hand side buys, at a use site. A guard is a constrained
zonotope — inequalities and all — and the set being cut is a constrained
polynomial zonotope, which is generally not convex. The guard converts exactly
and the intersection is exact, so nothing is given away in either step, and the
float layer does the same with `⊆` in place of `=`.

Neither line would elaborate against an equality-constrained representation. The
conversion would have needed a slack factor per inequality, and the float
intersection would have had nowhere to round: its agreement rows have to admit
the difference of two nominal points that each carry an error box.

The last example is the check that nothing was lost in the other direction: an
equality is still sayable, as the degenerate interval, and reads back as the
equation the paper writes.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open Matrix

variable {n : ℕ}

namespace Real

-- Anonymous, since their content is that they elaborate.

/-- A guard given by inequalities, met exactly by a set that need not be
convex. -/
example (cPZ : ConPolyZono (Vec ℝ n)) (G : ConZonotope (Vec ℝ n)) :
    cPZ.construct ∩ G.construct = (cPZ.intersection G.conPolyZono).construct := by
  rw [ConZonotope.conPolyZono_exact G]
  exact ConPolyZono.intersection_exact cPZ G.conPolyZono

/-- The paper's `A μ(α) = b`, as the degenerate interval. -/
example {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m) (R : Fin p → Fin s → ℕ)
    (a : Fin p → ℝ) (h : ConPolyZono.holds A (Interval.point b) R a) (i : Fin m) :
    (A *ᵥ PolyZonotope.monomial R a) i = b i :=
  (ConPolyZono.holds_point_iff A b R a).mp h i

end Real

namespace Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The same cut on a machine: the only non-convex intersection in this
repository that a float layer computes. -/
example (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (G : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ∩ G.construct ⊆ (cPZ.intersection G.conPolyZono).construct :=
  subset_trans (Set.inter_subset_inter subset_rfl (ConZonotope.conPolyZono_contains G))
    (ConPolyZono.intersection_outer cPZ G.conPolyZono)

end Float

end CORALean
