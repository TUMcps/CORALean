import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# How far the exact difference of two zonotopes reaches in one direction

The step [1, Thm. 5]'s proof needs before its linear program can be read: in
any direction `c`, the exact Minkowski difference reaches no further from
`c⁽ᵐ⁾ - c⁽ˢ⁾` than `Δd - Δd_trans` — the minuend's own reach in that direction
less the subtrahend's.

No halfspace description is assumed, and none is needed: the subtrahend's
farthest point in the direction `c` is written down explicitly, and the
minuend's reach is read off its generators. This is the *enclosing* half of
[1, Thm. 3], the half that holds for an arbitrary family of directions rather
than only for the minuend's own facet normals — the other half is what that
row defers, and what `minkDiffStretch_outer` therefore asks for.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Δd - Δd_trans` bounds the exact difference in the direction `c`, [1, Thm. 5]'s
`b̃` at its most conservative admissible value. -/
theorem Zonotope.minkowskiDiff_apply_le (Z₁ Z₂ : Zonotope α) (c : α →ₗ[ℝ] ℝ)
    {x : α} (hx : x ∈ minkowskiDiff Z₁.construct Z₂.construct) :
    c (x - (Z₁.c - Z₂.c)) ≤ (∑ υ, |c (Z₁.G υ)|) - ∑ υ, |c (Z₂.G υ)| := by -- --- PROOF ---
  -- the subtrahend's own farthest point in the direction `c`
  have hz : Z₂.c + ∑ j, (if 0 ≤ c (Z₂.G j) then (1:ℝ) else -1) • Z₂.G j ∈ Z₂.construct :=
    ⟨fun j => if 0 ≤ c (Z₂.G j) then (1:ℝ) else -1,
      fun j => by by_cases h : 0 ≤ c (Z₂.G j) <;> simp [h], rfl⟩
  obtain ⟨γ, hγ, hxz⟩ := hx _ hz
  have hσc : ∀ j, (if 0 ≤ c (Z₂.G j) then (1:ℝ) else -1) * c (Z₂.G j) = |c (Z₂.G j)| := by
    intro j
    by_cases h : 0 ≤ c (Z₂.G j)
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  -- read that membership through `c`, both sides
  have key := congrArg c hxz
  rw [map_add, map_add, map_sum, map_add, map_sum] at key
  simp only [map_smul, smul_eq_mul] at key
  rw [Finset.sum_congr rfl fun j _ => hσc j] at key
  have hb : ∑ i, γ i * c (Z₁.G i) ≤ ∑ i, |c (Z₁.G i)| :=
    Finset.sum_le_sum fun i _ => by
      calc γ i * c (Z₁.G i) ≤ |γ i * c (Z₁.G i)| := le_abs_self _
        _ = |γ i| * |c (Z₁.G i)| := abs_mul _ _
        _ ≤ 1 * |c (Z₁.G i)| := mul_le_mul_of_nonneg_right (hγ i) (abs_nonneg _)
        _ = |c (Z₁.G i)| := one_mul _
  rw [map_sub, map_sub]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
