module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The enclosing box encloses `Λ⁻¹ Z_∩`

The `box(Λ⁻¹ Z_∩)` of [1, Eq. 2] must contain `Λ⁻¹ Z_∩`, and does: the member-wise image
contains it (`SetIntersection.memberwise_outer` at `Zonotope.mtimes_exact`, [1, Prop. 1]) and
one member's box contains that member (`interval_contains`, [1, Prop. 6]).

## Inputs
* `Λ` – direction matrix
* `zB` – zonotope bundle
* `i` – member index

## Hypotheses
* none

## Conclusion
* the transformed bundle is contained in the enclosing box

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `enclosingBox` contains the image of the bundle under `Λ⁻¹`. -/
theorem ZonoBundle.enclosingBox_contains (Λ : Mat ℝ n n) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) :
    (fun x => Λ⁻¹ *ᵥ x) '' zB.construct ⊆ (zB.enclosingBox Λ i).construct :=
  (SetIntersection.memberwise_outer (Set.image (Λ⁻¹ *ᵥ ·)) Set.monotone_image fun i =>
    ⟨i, (Zonotope.mtimes_exact Λ⁻¹ (zB.Z i)).subset⟩).trans ((zB.mtimes Λ⁻¹).interval_contains i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
