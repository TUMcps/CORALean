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

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The centre, then each block's reach in turn: three directed roundings rather
than one, so no intermediate sum is ever rounded the wrong way. -/
def PolyZonotope.interval (pZ : PolyZonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  -- each block's reach, read off the generators laid out as CORA's `n × h` matrix
  let rG := radius fun i l => pZ.G l i
  let rGI := radius fun i j => pZ.GI j i
  { inf := fun i => subDown (subDown (subDown (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.err i)
    sup := fun i => addUp (addUp (addUp (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.err i) }

open SoundFloatArithmetic InflatedContSet

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.interval_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.interval.construct := by -- --- PROOF ---
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hzmem
  -- a monomial is at most one, so a dependent block reaches no further than a zonotope's
  have hdep := abs_sum_le_radius (d := fun i l => pZ.G l i) (Δ := fun i l => toReal (pZ.G l i))
    (β := fun l => Real.PolyZonotope.monomial pZ.E a l) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one pZ.E ha l) i
  have hind := abs_sum_le_radius (d := fun i j => pZ.GI j i) (Δ := fun i j => toReal (pZ.GI j i))
    (fun _ _ => le_refl _) hβ i
  set rG := radius fun i l => pZ.G l i
  set rGI := radius fun i j => pZ.GI j i
  have herr : |e i| ≤ toReal (PolyZonotope.errorBound pZ.err i) :=
    PolyZonotope.abs_le_errorBound (I := pZ.err) he i
  have hzi : z i = toReal (pZ.c i)
      + (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      + ∑ j, toReal (pZ.GI j i) * β j := hz i
  -- each face on its own, the three roundings all going away from the set
  constructor
  · have h1 := subDown_le_sub (subDown (subDown (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.err i)
    have h2 := subDown_le_sub (subDown (pZ.c i) (rG i)) (rGI i)
    have h3 := subDown_le_sub (pZ.c i) (rG i)
    show toReal (subDown (subDown (subDown (pZ.c i) (rG i)) (rGI i))
        (PolyZonotope.errorBound pZ.err i)) ≤ z i + e i
    rw [hzi]
    linarith [neg_le_of_abs_le hdep, neg_le_of_abs_le hind, neg_le_of_abs_le herr]
  · have h1 := add_le_addUp (addUp (addUp (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.err i)
    have h2 := add_le_addUp (addUp (pZ.c i) (rG i)) (rGI i)
    have h3 := add_le_addUp (pZ.c i) (rG i)
    show z i + e i ≤ toReal (addUp (addUp (addUp (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.err i))
    rw [hzi]
    linarith [le_of_abs_le hdep, le_of_abs_le hind, le_of_abs_le herr]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
