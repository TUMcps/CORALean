module

public import CORALean.ContSet.Zonotope.Real.Operations.Shear
public import CORALean.ContSet.Zonotope.Real.Theorems.MemWalkEdgesIff
public import CORALean.ContSet.Zonotope.Real.Theorems.ShearComb
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The walk edges of a sheared zonogon are the sheared walk edges

A sign corner of the sheared zonotope is the shear of the same sign corner, and the shear and its
inverse map a segment to the segment of the images. So `x` is on a walk edge of `Z.shear κ` exactly
when the unsheared point `(x₀ + κ x₁, x₁)` is on one of `Z`. With `mem_shear_construct` it carries a
vertical section theorem to every line `x - κ y = γ` ([1, Alg. 3]).

## Inputs
* `Z` – planar zonotope
* `κ` – shear factor
* `x` – point

## Hypotheses
* none

## Conclusion
* a point is on the sheared walk edges iff its unshear is on the original ones

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_shear_walkEdges (Z : Zonotope (Vec ℝ 2)) (κ : ℝ) (x : Vec ℝ 2) :
    x ∈ (Z.shear κ).walkEdges ↔
      (![x 0 + κ * x 1, x 1] : Vec ℝ 2) ∈ Z.walkEdges := by -- --- PROOF ---
  -- the shear and its inverse, as maps of the plane
  set f : Vec ℝ 2 → Vec ℝ 2 := fun z => ![z 0 - κ * z 1, z 1] with hf
  set g : Vec ℝ 2 → Vec ℝ 2 := fun z => ![z 0 + κ * z 1, z 1] with hg
  have hgf : ∀ z, g (f z) = z := fun z => by ext k; fin_cases k <;> simp [hf, hg]
  have hfg : ∀ z, f (g z) = z := fun z => by ext k; fin_cases k <;> simp [hf, hg]
  have hcorner : ∀ s : Fin Z.h → Bool, (Z.shear κ).corner s = f (Z.corner s) := fun s =>
    Zonotope.shear_comb Z κ (fun j => if s j = true then (1 : ℝ) else -1)
  -- a segment and its image under a map that is linear and has an inverse
  have hseg : ∀ A B x : Vec ℝ 2, x ∈ segment ℝ (f A) (f B) ↔ g x ∈ segment ℝ A B := by
    have hlin : ∀ (m : Vec ℝ 2 → Vec ℝ 2) (a b : ℝ) (A B : Vec ℝ 2),
        (∀ z w : Vec ℝ 2, ∀ s t : ℝ, m (s • z + t • w) = s • m z + t • m w) →
        m (a • A + b • B) = a • m A + b • m B := fun m a b A B h => h A B a b
    have hfl : ∀ z w : Vec ℝ 2, ∀ s t : ℝ, f (s • z + t • w) = s • f z + t • f w :=
      fun z w s t => by
      ext k; fin_cases k
      · simp [hf]; ring
      · simp [hf]
    have hgl : ∀ z w : Vec ℝ 2, ∀ s t : ℝ, g (s • z + t • w) = s • g z + t • g w :=
      fun z w s t => by
      ext k; fin_cases k
      · simp [hg]; ring
      · simp [hg]
    -- the segment of the images, by mapping with the map and with its inverse
    intro A B x
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      exact ⟨a, b, ha, hb, hab, by rw [hgl, hgf, hgf]⟩
    · rintro ⟨a, b, ha, hb, hab, h⟩
      refine ⟨a, b, ha, hb, hab, ?_⟩
      rw [← hfl, h, hfg]
  simp only [Zonotope.mem_walkEdges_iff, hcorner, hseg]
  exact Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
