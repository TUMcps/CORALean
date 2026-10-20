module

public import CORALean.Global.ConeEdge
public import CORALean.Global.EqSmulNCross
public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

@[expose] public section

/-!
# [1, Thm. 2]: a zonotope is its cross-product halfspaces

`C x ≤ d` at `C` the `2·C(p, n-1)` cross products of `n - 1` generators — here `n` of them in
`Vec ℝ (n + 1)`, the `±` pair read as an absolute value — and `d = C c + Δd` with
`Δd = ∑ᵤ |C G⁽ᵘ⁾|`. Equality, not enclosure: the enclosing half is free, and the other is that
those normals exhaust the facets, through a separating direction. A point outside the zonotope has
one; the signed generators make it a point of a pointed cone on which the separation is a positive
linear form; `exists_edge_of_cone` moves it to an edge of that cone, which `n` independent
generators annihilate; and `eq_smul_nCross` says the edge is a multiple of their cross product.
First appeared as [2, Thm. 7], its parallelotope case as [2, Lemma 6].

## Inputs
* `n` – dimension minus one
* `Z` – zonotope

## Hypotheses
* `hspan` – generators span the space

## Conclusion
* `Z` is the halfspace set cut out by the cross products

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: a zonotope whose generators span is exactly the halfspaces
their cross products cut out. -/
theorem Zonotope.hRep_eq {n : ℕ} (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) :
    Z.construct = {x | ∀ S : Fin n → Fin Z.h,
      |Z.facetNormal S ⬝ᵥ (x - Z.c)| ≤ ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ|} := by -- --- PROOF ---
  classical
  -- the generators span, so only `0` annihilates every one of them
  have hann : ∀ y : Vec ℝ (n + 1), (∀ υ, Z.G υ ⬝ᵥ y = 0) → y = 0 := by
    intro y hy
    refine dotProduct_self_eq_zero.mp (span_dotProduct_eq_zero Z.G y hy ?_)
    rw [hspan]
    exact Submodule.mem_top
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx => ?_)
  · -- the enclosing half: a bounded combination reaches no further than `Δd`
    obtain ⟨β, hβ, rfl⟩ := hx
    intro S
    have hsub : Z.c + (∑ υ, β υ • Z.G υ) - Z.c = ∑ υ, β υ • Z.G υ := by abel
    rw [hsub, dotProduct_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun υ _ => ?_)
    rw [dotProduct_smul, smul_eq_mul, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ υ)
  · -- the exhausting half, by contraposition: separate, then walk to an edge
    by_contra hxZ
    obtain ⟨f, u, hfZ, hfx⟩ :=
      geometric_hahn_banach_closed_point Z.convex_construct Z.isClosed_construct hxZ
    set r : Vec ℝ (n + 1) := fun i => f fun j => if i = j then (1 : ℝ) else 0 with hr
    have hfr : ∀ y : Vec ℝ (n + 1), f y = y ⬝ᵥ r := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    -- the zonotope's own farthest point in the direction `r`
    have hmem : Z.c + ∑ υ, (if 0 ≤ Z.G υ ⬝ᵥ r then (1 : ℝ) else -1) • Z.G υ ∈ Z.construct :=
      ⟨fun υ => if 0 ≤ Z.G υ ⬝ᵥ r then (1 : ℝ) else -1,
        fun υ => by by_cases h : 0 ≤ Z.G υ ⬝ᵥ r <;> simp [h], rfl⟩
    have hfar := hfZ _ hmem
    rw [hfr, add_dotProduct, sum_dotProduct] at hfar
    rw [hfr] at hfx
    have hsign : ∀ υ, ((if 0 ≤ Z.G υ ⬝ᵥ r then (1 : ℝ) else -1) • Z.G υ) ⬝ᵥ r
        = |Z.G υ ⬝ᵥ r| := by
      intro υ
      rw [smul_dotProduct, smul_eq_mul]
      by_cases h : 0 ≤ Z.G υ ⬝ᵥ r
      · rw [if_pos h, one_mul, abs_of_nonneg h]
      · rw [if_neg h, neg_one_mul, abs_of_neg (not_le.mp h)]
    rw [Finset.sum_congr rfl fun υ _ => hsign υ] at hfar
    -- the signed generators, a pointed cone whose interior `r` is in
    set ε : Fin Z.h → ℝˣ := fun υ => if 0 ≤ Z.G υ ⬝ᵥ r then 1 else -1 with hε
    set a : Fin Z.h → Vec ℝ (n + 1) := fun υ => (ε υ : ℝ) • Z.G υ with ha
    have habs : ∀ (υ) (y : Vec ℝ (n + 1)), |a υ ⬝ᵥ y| = |Z.G υ ⬝ᵥ y| := by
      intro υ y
      rw [ha, smul_dotProduct, smul_eq_mul, abs_mul, hε]
      by_cases h : 0 ≤ Z.G υ ⬝ᵥ r <;> simp [h]
    have hzero : ∀ (υ) (y : Vec ℝ (n + 1)), a υ ⬝ᵥ y = 0 ↔ Z.G υ ⬝ᵥ y = 0 := by
      intro υ y
      rw [← abs_eq_zero, habs υ y, abs_eq_zero]
    have har : ∀ υ, 0 ≤ a υ ⬝ᵥ r := by
      intro υ
      rw [ha, smul_dotProduct, smul_eq_mul, hε]
      by_cases h : 0 ≤ Z.G υ ⬝ᵥ r <;> simp [h]
      linarith [not_le.mp h]
    have hpt : ∀ y : Vec ℝ (n + 1), (∀ υ, a υ ⬝ᵥ y = 0) → y = 0 :=
      fun y hy => hann y fun υ => (hzero υ y).mp (hy υ)
    -- the form the separation leaves, and the edge it is still positive on
    set w : Vec ℝ (n + 1) := (x - Z.c) - ∑ υ, a υ with hw
    have hwr : 0 < w ⬝ᵥ r := by
      rw [hw, sub_dotProduct, sub_dotProduct, sum_dotProduct]
      have : ∀ υ, a υ ⬝ᵥ r = |Z.G υ ⬝ᵥ r| := fun υ => by
        rw [← abs_of_nonneg (har υ), habs υ r]
      rw [Finset.sum_congr rfl fun υ _ => this υ]
      linarith
    obtain ⟨S, y, hind, hSy, hy, hwy⟩ := exists_edge_of_cone a w hpt r har hwr
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, dotProduct_zero] at hwy
      exact lt_irrefl 0 hwy
    -- the edge is a multiple of the cross product of the generators it annihilates
    have hGy : ∀ i, Z.G (S i) ⬝ᵥ y = 0 := fun i => (hzero (S i) y).mp (hSy i)
    have hindG : LinearIndependent ℝ fun i => Z.G (S i) := by
      have hsm : (fun i => a (S i)) = (fun i => ε (S i)) • fun i => Z.G (S i) := rfl
      rw [hsm] at hind
      exact (LinearIndependent.units_smul_iff _ _).mp hind
    obtain ⟨lam, hlam, hyl⟩ :=
      eq_smul_nCross (Matrix.of fun i j => Z.G (S j) i) y hy0 hGy hindG
    -- what `w ⬝ᵥ y > 0` says once the multiple is divided out
    have hgen : ∀ υ, a υ ⬝ᵥ y = |Z.G υ ⬝ᵥ y| := fun υ => by
      rw [← abs_of_nonneg (hy υ), habs υ y]
    have hkey : ∑ υ, |Z.G υ ⬝ᵥ y| < (x - Z.c) ⬝ᵥ y := by
      rw [hw, sub_dotProduct, sum_dotProduct] at hwy
      rw [Finset.sum_congr rfl fun υ _ => hgen υ] at hwy
      linarith
    -- and the hypothesis at `S`, which it contradicts
    have hxS := hx S
    rw [Zonotope.facetNormal] at hxS
    rw [hyl] at hkey
    simp only [dotProduct_smul, smul_eq_mul, abs_mul, ← Finset.mul_sum] at hkey
    have hlampos : 0 < |lam| := abs_pos.mpr hlam
    have hbound : ∑ υ, |Z.G υ ⬝ᵥ nCross (Matrix.of fun i j => Z.G (S j) i)|
        < |(x - Z.c) ⬝ᵥ nCross (Matrix.of fun i j => Z.G (S j) i)| := by
      have hle : lam * ((x - Z.c) ⬝ᵥ nCross (Matrix.of fun i j => Z.G (S j) i))
          ≤ |lam| * |(x - Z.c) ⬝ᵥ nCross (Matrix.of fun i j => Z.G (S j) i)| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith [hkey, hle]
    rw [dotProduct_comm] at hxS
    refine absurd hxS (not_le.mpr ?_)
    refine lt_of_le_of_lt (le_of_eq ?_) hbound
    exact Finset.sum_congr rfl fun υ _ => by rw [dotProduct_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
