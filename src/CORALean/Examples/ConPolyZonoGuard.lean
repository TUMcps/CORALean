import CORALean.ContSet.ConPolyZono.Float.Theorems.AndOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact
import CORALean.ContSet.Conversion.Float.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono

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

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

open Matrix

variable {n : ℕ}

namespace Real

-- Anonymous, since their content is that they elaborate.

/-- A guard given by inequalities, met exactly by a set that need not be
convex. -/
example (C : ConPolyZono (Vec ℝ n)) (G : ConZonotope (Vec ℝ n)) :
    C.construct ∩ G.construct = (C.and G.conPolyZono).construct := by
  rw [ConZonotope.conPolyZono_exact G]
  exact ConPolyZono.and_exact C G.conPolyZono

/-- The paper's `A μ(α) = b`, as the degenerate interval. -/
example {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m) (EC : Fin p → Fin s → ℕ)
    (a : Fin p → ℝ) (h : ConPolyZono.holds A (Interval.point b) EC a) (i : Fin m) :
    (A *ᵥ PolyZonotope.monomial EC a) i = b i :=
  (ConPolyZono.holds_point_iff A b EC a).mp h i

end Real

namespace Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The same cut on a machine: the only non-convex intersection in this
repository that a float layer computes. -/
example (C : ConPolyZono 𝕋 n) (G : ConZonotope 𝕋 n) :
    C.construct ∩ G.construct ⊆ (C.and G.conPolyZono).construct :=
  subset_trans (Set.inter_subset_inter subset_rfl (ConZonotope.conPolyZono_outer G))
    (ConPolyZono.and_outer C G.conPolyZono)

end Float

end CORALean
