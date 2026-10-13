import CORALean.ContSet.ConZonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsConstructEqImageFst
import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Constrained zonotopes are exactly the bounded polytopes

[1, Thm. 1]: a set is a constrained zonotope iff it is a convex polytope, a bounded halfspace
description. The "if" half is `HPolytope.conZonotope_exact`, [1]'s eq. 21, with the box it
needs read off the boundedness. The "only if" half, which [1] dismisses with "clearly": a
constrained zonotope `{c + Gξ | ‖ξ‖∞ ≤ 1, ξ ∈ P}` is the projection onto `x` of the polytope
`{(x, ξ) | ‖ξ‖∞ ≤ 1, ξ ∈ P, x = c + Gξ}`, and a projection of a halfspace description is one
(`HPolytope.exists_construct_eq_image_fst`, Fourier–Motzkin). Bounded it is, being compact.

The constraint on the coefficients is any halfspace description, of which [1]'s `Aξ = b` is
the equality-only case, so the theorem covers [1]'s Definition 3 and more.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A constrained zonotope is a halfspace description: the shadow of the lifted polytope. -/
theorem ConZonotope.aux_exists_hPolytope (cZ : ConZonotope (Vec ℝ n)) :
    ∃ P : HPolytope (Vec ℝ n), P.construct = cZ.construct := by -- --- PROOF ---
  -- `x = c + Gξ`, one equality per coordinate
  let graph : HPolytope (Vec ℝ n × Vec ℝ cZ.h) :=
    { m := 0, A := Fin.elim0, b := Fin.elim0, me := n,
      Ae := fun i => (LinearMap.proj i).comp (LinearMap.fst ℝ _ _)
        - ∑ j, cZ.G j i • (LinearMap.proj j).comp (LinearMap.snd ℝ _ _),
      be := fun i => cZ.c i }
  -- the lifted polytope: the unit box and `P` on `ξ`, and the graph
  let L := (((HPolytope.unitBox cZ.h).comap (LinearMap.snd ℝ _ _)).intersection
    (cZ.P.comap (LinearMap.snd ℝ _ _))).intersection graph
  obtain ⟨Q, hQ⟩ := HPolytope.exists_construct_eq_image_fst L
  refine ⟨Q, hQ.trans ?_⟩
  -- the graph's equalities say `x = c + Gξ`
  have hgraph : ∀ x ξ, (x, ξ) ∈ graph.construct ↔ x = cZ.c + ∑ j, ξ j • cZ.G j := by
    intro x ξ
    constructor
    · rintro ⟨-, h⟩
      funext i
      have := h i
      simp only [graph, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_proj, Function.eval, LinearMap.fst_apply, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, LinearMap.snd_apply, smul_eq_mul] at this
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      linarith [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
        (mul_comm (cZ.G j i) (ξ j))]
    -- and back: `c + Gξ` meets every equality
    · rintro rfl
      refine ⟨fun i => i.elim0, fun i => ?_⟩
      simp only [graph, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_proj, Function.eval, LinearMap.fst_apply, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, LinearMap.snd_apply, smul_eq_mul,
        Pi.add_apply, Pi.smul_apply]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => mul_comm (cZ.G j i) (ξ j)]
      ring
  -- the shadow is the constrained zonotope
  ext x
  simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, L,
    HPolytope.mem_intersection_iff, HPolytope.comap, ConZonotope.construct]
  constructor
  · rintro ⟨ξ, ⟨hbox, hP⟩, hg⟩
    refine ⟨ξ, HPolytope.mem_unitBox_iff.mp hbox, hP, (hgraph x ξ).mp hg⟩
  · rintro ⟨ξ, hbox, hP, rfl⟩
    exact ⟨ξ, ⟨HPolytope.mem_unitBox_iff.mpr hbox, hP⟩, (hgraph _ ξ).mpr rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a set is a constrained zonotope iff it is a bounded halfspace description. -/
theorem ConZonotope.exists_construct_eq_iff_hPolytope {S : Set (Vec ℝ n)} :
    (∃ cZ : ConZonotope (Vec ℝ n), cZ.construct = S) ↔
      ∃ P : HPolytope (Vec ℝ n),
        P.construct = S ∧ Bornology.IsBounded S := by -- --- PROOF ---
  constructor
  · rintro ⟨cZ, rfl⟩
    obtain ⟨P, hP⟩ := cZ.aux_exists_hPolytope
    exact ⟨P, hP, cZ.isBounded_construct⟩
  · rintro ⟨P, rfl, hb⟩
    -- the box [1]'s eq. 21 needs, from any ball around the polytope
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    have hcoord : ∀ x ∈ P.construct, ∀ j, |x j| ≤ R := fun x hx j =>
      (Real.norm_eq_abs _ ▸ norm_le_pi_norm x j).trans (mem_closedBall_zero_iff.mp (hR hx))
    exact ⟨HPolytope.conZonotope (fun j => ⟨R, fun x hx => (le_abs_self _).trans (hcoord x hx j)⟩)
      (fun j => ⟨R, fun x hx => (neg_le_abs _).trans (hcoord x hx j)⟩),
      HPolytope.conZonotope_exact _ _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
