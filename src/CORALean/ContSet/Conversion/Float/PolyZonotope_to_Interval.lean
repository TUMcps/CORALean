import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# A polynomial zonotope as a box, over a floating-point scalar

The centre give or take what each block can reach: the dependent generators, the
independent ones, and the error box, every end rounded away from the set.

Direct, where the exact layer's route frees the dependent generators into a
zonotope first. There is no float `PolyZonotope.zonotope` to go through, and
nothing would be gained by one — freeing a generator is what costs the exact
route its precision, and both routes are equally loose about a monomial that
never reaches `-1`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The centre, then each block's reach in turn: three directed roundings rather
than one, so no intermediate sum is ever rounded the wrong way. -/
def PolyZonotope.interval (PZ : PolyZonotope 𝕋 n) : Interval 𝕋 n where
  inf := fun i => subDown (subDown (subDown (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
    (PolyZonotope.errorBound PZ.err i)
  sup := fun i => addUp (addUp (addUp (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
    (PolyZonotope.errorBound PZ.err i)

open SoundFloatArithmetic InflatedContSet

variable [SoundFloatArithmetic 𝕋]

theorem PolyZonotope.interval_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.interval.construct := by
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hzmem
  -- a monomial is at most one, so a dependent block reaches no further than a zonotope's
  have hdep := abs_sum_le_radius (d := PZ.G) (Δ := fun i l => toReal (PZ.G i l))
    (β := fun l => Real.PolyZonotope.monomial PZ.E a l) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one PZ.E ha l) i
  have hind := abs_sum_le_radius (d := PZ.GI) (Δ := fun i j => toReal (PZ.GI i j))
    (fun _ _ => le_refl _) hβ i
  have herr : |e i| ≤ toReal (PolyZonotope.errorBound PZ.err i) :=
    PolyZonotope.abs_le_errorBound (I := PZ.err) he i
  have hzi : z i = toReal (PZ.c i)
      + (∑ l, toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
      + ∑ j, toReal (PZ.GI i j) * β j := hz i
  -- each face on its own, the three roundings all going away from the set
  constructor
  · have h1 := subDown_le_sub (subDown (subDown (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
      (PolyZonotope.errorBound PZ.err i)
    have h2 := subDown_le_sub (subDown (PZ.c i) (radius PZ.G i)) (radius PZ.GI i)
    have h3 := subDown_le_sub (PZ.c i) (radius PZ.G i)
    show toReal (subDown (subDown (subDown (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
        (PolyZonotope.errorBound PZ.err i)) ≤ z i + e i
    rw [hzi]
    linarith [neg_le_of_abs_le hdep, neg_le_of_abs_le hind, neg_le_of_abs_le herr]
  · have h1 := add_le_addUp (addUp (addUp (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
      (PolyZonotope.errorBound PZ.err i)
    have h2 := add_le_addUp (addUp (PZ.c i) (radius PZ.G i)) (radius PZ.GI i)
    have h3 := add_le_addUp (PZ.c i) (radius PZ.G i)
    show z i + e i ≤ toReal (addUp (addUp (addUp (PZ.c i) (radius PZ.G i)) (radius PZ.GI i))
      (PolyZonotope.errorBound PZ.err i))
    rw [hzi]
    linarith [le_of_abs_le hdep, le_of_abs_le hind, le_of_abs_le herr]

end CORALean.Float
