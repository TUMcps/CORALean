module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeConZonotopeExact
public import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection
public import CORALean.ContSet.Zonotope.Real.Operations.GenMap
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope

@[expose] public section

/-!
# A constrained zonotope is exactly a bounded affine image of a polytope

`[1, Thm. 4]`: a non-empty set is a constrained zonotope iff it is an
"AH-polytope", an affine image `xbar + X·P` of an H-Rep polytope `P` (`[1, Def.
1]`, itself restated from Sadraddini and Tedrake). Both halves are already
here under other names: `construct_eq_image` reads a constrained zonotope this
way with `X` its own generator map and `P` its `domain`; `HPolytope.conZonotope`
is `[1]`'s "Theorem 1 of Scott et al." the other way, an H-Rep polytope as a
constrained zonotope, composed here with `map` for the linear part and a
center shift for the rest. `P` bounded (a `SupportBound` pair per coordinate)
is `[1]`'s own assumption made explicit: its "polytope" is bounded, while an
H-Rep `P` here need not be. Non-emptiness is not needed — the iff holds at `∅`
too, which an infeasible constrained zonotope denotes.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Shifting a constrained zonotope's center shifts its construct by the same
amount — the translation half of an affine image. -/
theorem ConZonotope.aux_construct_shift (cZ : ConZonotope (Vec ℝ n)) (v : Vec ℝ n) :
    ({ cZ with c := v + cZ.c } : ConZonotope (Vec ℝ n)).construct
      = (fun y => v + y) '' cZ.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩
    exact ⟨cZ.c + ∑ j, β j • cZ.G j, ⟨β, hβ, hP, rfl⟩, by module⟩
  · rintro ⟨y, ⟨β, hβ, hP, rfl⟩, rfl⟩
    exact ⟨β, hβ, hP, by module⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.eq_construct_iff_isAffineImage {S : Set (Vec ℝ n)} :
    (∃ cZ : ConZonotope (Vec ℝ n), cZ.construct = S) ↔
      ∃ (m : ℕ) (X : Vec ℝ m →ₗ[ℝ] Vec ℝ n) (xbar : Vec ℝ n) (P : HPolytope (Vec ℝ m))
        (_ : ∀ j, SupportBound P.construct (LinearMap.proj j))
        (_ : ∀ j, SupportBound P.construct (-LinearMap.proj j)),
        (fun ξ => xbar + X ξ) '' P.construct = S := by -- --- PROOF ---
  constructor
  -- a constrained zonotope's own generators are its affine map, its domain the polytope
  · rintro ⟨cZ, rfl⟩
    have hsub : cZ.domain.construct ⊆ (HPolytope.unitBox cZ.h).construct :=
      fun _ hx => (HPolytope.mem_intersection_iff.mp hx).1
    refine ⟨cZ.h, (⟨cZ.h, cZ.c, cZ.G⟩ : Zonotope (Vec ℝ n)).genMap, cZ.c, cZ.domain,
      fun j => ⟨1, fun x hx => (abs_le.mp (HPolytope.mem_unitBox_iff.mp (hsub hx) j)).2⟩,
      fun j => ⟨1, fun x hx => by
        have h := (abs_le.mp (HPolytope.mem_unitBox_iff.mp (hsub hx) j)).1
        show -(x j) ≤ 1
        linarith⟩, ?_⟩
    have hfun : (fun ξ : Vec ℝ cZ.h => cZ.c + (⟨cZ.h, cZ.c, cZ.G⟩ : Zonotope (Vec ℝ n)).genMap ξ)
        = fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j := by
      funext ξ; rfl
    rw [hfun]
    exact (ConZonotope.construct_eq_image cZ).symm
  -- back: Scott et al.'s conversion gives the polytope as a constrained zonotope, `map` the rest
  · rintro ⟨m, X, xbar, P, up, lo, rfl⟩
    refine ⟨{ (HPolytope.conZonotope up lo).map X with
        c := xbar + ((HPolytope.conZonotope up lo).map X).c }, ?_⟩
    rw [ConZonotope.aux_construct_shift, ← ConZonotope.map_exact, HPolytope.conZonotope_exact,
      Set.image_image]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
