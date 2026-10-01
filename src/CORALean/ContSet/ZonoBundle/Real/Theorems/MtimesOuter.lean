import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# `ZonoBundle.mtimes` over-approximates the linear image

Sound because `M (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ M Zᵢ` [1, Prop. 1]: a point in every component maps into
every image, `Zonotope.mtimes_exact` reading that image back as the one
component of the mapped bundle it came from.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimes_outer (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) :
    (M *ᵥ ·) '' zB.construct ⊆ (zB.mtimes M).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show M *ᵥ a ∈ (Zonotope.mtimes M (zB.Z i)).construct
  rw [← Zonotope.mtimes_exact]
  exact ⟨a, ha _, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
