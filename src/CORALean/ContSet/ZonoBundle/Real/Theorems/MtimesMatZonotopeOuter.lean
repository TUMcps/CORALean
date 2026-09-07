import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesMatZonotopeOuter

/-!
# `ZonoBundle.mtimesMatZonotope` over-approximates every matrix it denotes

Sound because `A (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ A Zᵢ` for each denoted `A`: a point in every
component maps into every image, and `Zonotope.mtimesMatZonotope_outer` then
encloses that image in the component of the mapped bundle it came from.

Weaker than a componentwise reading suggests: the outer union quantifies over
the matrices once, ahead of the intersection, so the enclosure is allowed to
pick a different `A` per component even though the hypothesis supplies one.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimesMatZonotope_outer (M : Zonotope (Mat ℝ m n))
    (zB : ZonoBundle (Vec ℝ n)) :
    (⋃ A ∈ M.construct, (A *ᵥ ·) '' zB.construct)
      ⊆ (zB.mtimesMatZonotope M).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, a, ha, rfl⟩ := hy
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show A *ᵥ a ∈ (Zonotope.mtimesMatZonotope M (zB.Z i)).construct
  exact Zonotope.mtimesMatZonotope_outer M (zB.Z i) (Set.mem_biUnion hA ⟨a, ha i, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
