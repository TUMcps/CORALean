import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.Basic
import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeConPolyZonoContains
import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConPolyZonoExact
import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact

/-!
# Cutting a non-convex set by a guard

A guard is a constrained zonotope — inequalities and all — and the set being cut is a
constrained polynomial zonotope, which is generally not convex. The guard converts exactly, an
inequality row becoming an equation with a slack factor (`ConPolyZono.relax`), and the
intersection is exact, so nothing is given away in either step; the float layer does the same with
`⊆` in place of `=`, its rows' rounding recorded in `b_error`.

The last example reads the constraint back as what it is: the paper's `A μ(α) = b`, a polynomial
level set on the factors with `=` in every row.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
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

/-- The paper's `A μ(α) = b` is the factor constraint, a polynomial level set with `=` rows. -/
example (cPZ : ConPolyZono (Vec ℝ n)) (a : Fin cPZ.p → ℝ) (h : cPZ.satisfies a) :
    a ∈ cPZ.cons.construct :=
  (ConPolyZono.satisfies_iff_mem_cons cPZ a).mp h

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
