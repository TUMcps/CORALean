import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A zonotope as a polynomial zonotope

Exact, and the cleanest check on the definition: give each generator a factor of
its own, appearing in that generator alone and to the first power, and every
monomial collapses to the coefficient it stands for. The exponent matrix is the
identity, and `GI` is empty — a zonotope's coefficients are all dependent, since
with one factor each there is nothing for them to depend on.

Read the other way, a polynomial zonotope is a zonotope exactly when its
exponent matrix can be brought to this shape.

Both directions are stated through `show`: the counts of the result are
projections of a definition, and only in their reduced spelling do the sum
lemmas match.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def Zonotope.polyZonotope (Z : Zonotope α) : PolyZonotope α where
  p := Z.h
  h := Z.h
  q := 0
  c := Z.c
  G := Z.G
  E := PolyZonotope.identE Z.h
  GI := Fin.elim0

theorem Zonotope.polyZonotope_exact (Z : Zonotope α) :
    Z.construct = Z.polyZonotope.construct := by
  have hsum : ∀ a : Fin Z.h → ℝ,
      (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) a i • Z.G i)
        = ∑ j, a j • Z.G j :=
    fun a => Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_identE]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    refine ⟨β, fun _ => 0, hβ, fun j => j.elim0, ?_⟩
    show Z.c + ∑ j, β j • Z.G j
        = Z.c + (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) β i • Z.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [hsum]
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨a, ha, ?_⟩
    show Z.c + (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) a i • Z.G i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = Z.c + ∑ j, a j • Z.G j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [hsum]
    rfl

end CORALean.Real
