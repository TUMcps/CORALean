module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The unit ball of the zonotope norm is the zonotope

`[1, Cor. 1]`: for a non-degenerate `Z = ⟨c, G⟩`, `B^Z_1(c) = Z` and `C^Z_1(c) = ∂Z`. The
first is the definition read back: `|γⱼ| ≤ 1` for all `j` is `‖γ‖∞ ≤ 1`, and the minimum is
attained. The second needs `ν` continuous (it is Lipschitz, `exists_lipschitzWith_coeffNorm`):
then `{ν < 1}` is open, so interior, and a point with `ν = 1` is a limit of the points
`c + t (p - c)`, `t > 1`, outside `Z`.

## Inputs
* `Z` – zonotope

## Hypotheses
* `hG` – generator map surjective

## Conclusion
* the unit ball and sphere of the norm are `Z` and its frontier

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_ball_eq (Z : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z.genMap) :
    {x | Z.zonotopeNorm (x - Z.c) ≤ 1} = Z.construct ∧
      {x | Z.zonotopeNorm (x - Z.c) = 1} = frontier Z.construct := by -- --- PROOF ---
  -- `x ∈ Z` iff some `γ` with `‖γ‖∞ ≤ 1` reaches `x - c`
  have hball : {x | Z.zonotopeNorm (x - Z.c) ≤ 1} = Z.construct := by
    ext x
    simp only [Set.mem_setOf_eq, Zonotope.zonotopeNorm, coeffNorm_le_iff _ (hG (x - Z.c))]
    constructor
    · rintro ⟨γ, hγ, hn⟩
      refine ⟨γ, fun j => ?_, ?_⟩
      · exact (norm_le_pi_norm γ j).trans hn
      · have : Z.genMap γ = ∑ j, γ j • Z.G j := rfl
        rw [← this, hγ]; abel
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨γ, by simp [Zonotope.genMap], (pi_norm_le_iff_of_nonneg zero_le_one).mpr hγ⟩
  refine ⟨hball, ?_⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm Z.genMap hG
  have hcont : Continuous fun x => Z.zonotopeNorm (x - Z.c) :=
    hK.continuous.comp (continuous_id.sub continuous_const)
  -- the interior is `{ν < 1}`
  have hint : interior Z.construct = {x | Z.zonotopeNorm (x - Z.c) < 1} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hle : Z.zonotopeNorm (x - Z.c) ≤ 1 := by
        have := interior_subset hx
        rw [← hball] at this
        exact this
      refine lt_of_le_of_ne hle fun heq => ?_
      obtain ⟨ε, hε, hεx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
      have hne : x - Z.c ≠ 0 := fun h0 => by
        rw [h0, Zonotope.zonotopeNorm, coeffNorm_zero] at heq; norm_num at heq
      have hnpos : 0 < ‖x - Z.c‖ := norm_pos_iff.mpr hne
      -- `y = x + δ (x - c)` is close to `x` and has `ν(y - c) = 1 + δ`
      set δ := ε / (2 * ‖x - Z.c‖) with hδ
      have hδ0 : 0 < δ := by positivity
      have hy : x + δ • (x - Z.c) ∈ Z.construct := by
        refine interior_subset (hεx ?_)
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hδ0, hδ]
        have : ε / (2 * ‖x - Z.c‖) * ‖x - Z.c‖ = ε / 2 := by field_simp
        rw [this]
        linarith
      -- yet `y ∈ Z` would need `1 + δ ≤ 1`
      rw [← hball] at hy
      have : Z.zonotopeNorm (x + δ • (x - Z.c) - Z.c) = 1 + δ := by
        rw [show x + δ • (x - Z.c) - Z.c = (1 + δ) • (x - Z.c) by module, Zonotope.zonotopeNorm,
          coeffNorm_smul _ (hG _), ← Zonotope.zonotopeNorm, heq, abs_of_pos (by linarith),
          mul_one]
      simp only [Set.mem_setOf_eq, this] at hy
      linarith
    -- `{ν < 1}` is open, so inside the interior
    · have hopen : IsOpen {x | Z.zonotopeNorm (x - Z.c) < 1} := isOpen_lt hcont continuous_const
      refine interior_maximal ?_ hopen
      intro x hx
      rw [← hball]
      exact le_of_lt (Set.mem_setOf_eq ▸ hx)
  have hclosed : IsClosed Z.construct := by
    rw [← hball]; exact isClosed_le hcont continuous_const
  rw [hclosed.frontier_eq, hint, ← hball]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_sdiff, not_lt]
  constructor
  · intro h; exact ⟨h.le, h.ge⟩
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
