import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.GenMap
import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact

/-!
# A halfspace description as a constrained zonotope

Exact, and the conversion that shows what constrained zonotopes are for: any
bounded halfspace description is one, with the rows kept rather than
approximated.

The generators come from a box enclosure — anything containing the polytope
would do — and the rows are then carried onto the coefficients by composing with
the generator map, after shifting by the centre. What the coefficients must
satisfy is exactly what the original rows said, so nothing is lost; the box is
only there to supply generators, and drops out.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.conZonotope
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ConZonotope (Vec ℝ n) where
  h := (HPolytope.zonotope up lo).h
  c := (HPolytope.zonotope up lo).c
  G := (HPolytope.zonotope up lo).G
  P := (P.translate (-(HPolytope.zonotope up lo).c)).comap (HPolytope.zonotope up lo).genMap

theorem HPolytope.conZonotope_exact
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    (HPolytope.conZonotope up lo).construct = P.construct := by
  -- the coefficients' constraint says exactly that the point they name is in `P`
  have hmem : ∀ β : Vec ℝ (HPolytope.zonotope up lo).h,
      β ∈ ((P.translate (-(HPolytope.zonotope up lo).c)).comap
            (HPolytope.zonotope up lo).genMap).construct
        ↔ (HPolytope.zonotope up lo).c + (HPolytope.zonotope up lo).genMap β ∈ P.construct := by
    intro β
    rw [HPolytope.comap_exact, Set.mem_preimage, ← HPolytope.translate_exact]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h : (HPolytope.zonotope up lo).genMap β = -(HPolytope.zonotope up lo).c + y := hxy.symm
      rw [h]
      simpa using hy
    · intro h
      exact ⟨(HPolytope.zonotope up lo).c + (HPolytope.zonotope up lo).genMap β, h, by abel⟩
  ext x
  constructor
  · rintro ⟨β, -, hP, rfl⟩
    exact (hmem β).mp hP
  · intro hx
    obtain ⟨β, hβ, hxβ⟩ := HPolytope.subset_zonotope up lo hx
    refine ⟨β, hβ, (hmem β).mpr ?_, hxβ⟩
    show (HPolytope.zonotope up lo).c + ∑ j, β j • (HPolytope.zonotope up lo).G j ∈ P.construct
    rwa [← hxβ]

end CORALean.Real
