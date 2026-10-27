module

public import CORALean.ContSet.Zonotope.Real.Operations.Polymax
public import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormBallEq
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `polymax` decides containment

`[1, Alg. 2]` is exact for a non-degenerate `Z₂` given exactly by its facets `{H x ≤ h}`
(moved to the origin, every `hᵢ ≠ 0`): a point of `Z₁` outside `Z₂` violates some facet
`i`, and the vertex `vᵢ` maximizes `ηᵢ` over `Z₁` — `hᵢ > 0` since `0` is inside, so the
sign of `ηᵢ gⱼ / hᵢ` is that of `ηᵢ gⱼ` — so `vᵢ` violates it too, and `‖vᵢ - c₂‖ > 1`.
Conversely every `vᵢ` is a point of `Z₁`.

## Inputs
* `Z₁` – zonotope tested
* `Z₂` – containing zonotope
* `H` – facet matrix
* `h` – facet offsets

## Hypotheses
* `hG` – generator map of `Z₂` surjective
* `hrep` – facets describe `Z₂` around its center
* `hne` – offsets nonzero

## Conclusion
* the test is true iff `Z₁` lies in `Z₂`

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.polymax_iff (Z₁ Z₂ : Zonotope (Vec ℝ n)) (hG : Function.Surjective Z₂.genMap)
    {H : Mat ℝ s n} {h : Vec ℝ s}
    (hrep : (HPolytope.ineqs H h).construct = {y | Z₂.c + y ∈ Z₂.construct})
    (hne : ∀ i, h i ≠ 0) : -- --- CONCL ---
    Z₁.polymax Z₂ H h = true ↔ Z₁.construct ⊆ Z₂.construct := by -- --- PROOF ---
  have hball := (Z₂.zonotopeNorm_ball_eq hG).1
  set x : Fin s → Fin Z₁.h → ℝ := fun i j => if (H *ᵥ Z₁.G j) i / h i ≥ 0 then 1 else -1
    with hx
  set v : Fin s → Vec ℝ n := fun i => Z₁.c + ∑ j, x i j • Z₁.G j with hv
  -- the test is that every `vᵢ` lies in `Z₂`
  have htest : Z₁.polymax Z₂ H h = true ↔ ∀ i, v i ∈ Z₂.construct := by
    simp only [Zonotope.polymax, gt_iff_lt, not_lt, ite_eq_left_iff, Bool.false_eq_true,
      imp_false, not_not]
    rw [← hball]
    rfl
  have hxabs : ∀ i j, |x i j| ≤ 1 := fun i j => by simp only [hx]; split_ifs <;> simp
  rw [htest]
  constructor
  · intro hvin p hp
    -- every right-hand side is positive, `0` being inside
    have hpos : ∀ i, 0 < h i := fun i => by
      have h0 : (0 : Vec ℝ n) ∈ (HPolytope.ineqs H h).construct := by
        rw [hrep]; simpa using Z₂.center_mem_construct
      have := HPolytope.mem_ineqs_iff.mp h0 i
      simp only [mulVec_zero, Pi.zero_apply] at this
      exact lt_of_le_of_ne this (hne i).symm
    -- `p - c₂` meets every facet `vᵢ - c₂` meets
    obtain ⟨β, hβ, rfl⟩ := hp
    have hmem : Z₁.c + ∑ j, β j • Z₁.G j - Z₂.c ∈ (HPolytope.ineqs H h).construct := by
      refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
      have hvi : v i - Z₂.c ∈ (HPolytope.ineqs H h).construct := by
        rw [hrep]; simpa using hvin i
      refine le_trans ?_ (HPolytope.mem_ineqs_iff.mp hvi i)
      -- `vᵢ` takes each generator with the sign of `ηᵢ gⱼ`, which is the most `βⱼ` can give
      simp only [hv, mulVec_sub, mulVec_add, mulVec_sum, mulVec_smul, Pi.sub_apply,
        Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hsum : ∑ j, β j * (H *ᵥ Z₁.G j) i ≤ ∑ j, x i j * (H *ᵥ Z₁.G j) i :=
        Finset.sum_le_sum fun j _ => ?_
      · linarith
      -- `βⱼ (ηᵢ gⱼ) ≤ |ηᵢ gⱼ| = xᵢⱼ (ηᵢ gⱼ)`
      by_cases hs : (H *ᵥ Z₁.G j) i ≥ 0
      · have : x i j = 1 := by simp [hx, div_nonneg hs (hpos i).le]
        rw [this, one_mul]
        nlinarith [(abs_le.mp (hβ j)).2]
      · have : x i j = -1 := by
          simp only [hx]
          rw [if_neg]
          intro hge
          have hge' : 0 ≤ (H *ᵥ Z₁.G j) i ∧ 0 ≤ h i := by
            simpa [div_nonneg_iff, (hpos i).not_ge, hpos i] using hge
          exact hs hge'.1
        rw [this]
        push Not at hs
        nlinarith [(abs_le.mp (hβ j)).1]
    rw [hrep] at hmem
    simpa using hmem
  · intro hsub i
    exact hsub ⟨fun j => x i j, hxabs i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
