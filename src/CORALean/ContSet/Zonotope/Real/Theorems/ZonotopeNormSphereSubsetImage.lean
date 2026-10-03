import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# The unit circle of the zonotope norm, against the image of the cube's boundary

`[1, Remark 1]`: `G (∂[-1, 1]^m) ⊇ C^Z_1(0)` always, and the converse can fail. A point with
`ν = 1` has a minimizer with `‖γ‖∞ = 1`, a point of the cube's boundary; but `G = (1, 1)`
sends the boundary point `(1, 0)` to `1`, whose norm is `1/2`. The cube's boundary is
the unit sphere of `‖·‖∞`, and is written so.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_sphere_subset_image :
    (∀ (n : ℕ) (Z : Zonotope (Vec ℝ n)), Function.Surjective Z.genMap → ∀ x,
      Z.zonotopeNorm x = 1 → ∃ γ, ‖γ‖ = 1 ∧ Z.genMap γ = x) ∧
    ∃ Z : Zonotope (Vec ℝ 1), Function.Surjective Z.genMap ∧
      ∃ γ, ‖γ‖ = 1 ∧ Z.zonotopeNorm (Z.genMap γ) ≠ 1 := by -- --- PROOF ---
  refine ⟨fun n Z hG x hx => ?_, ?_⟩
  -- a minimizer has norm `ν x = 1`
  · obtain ⟨γ, hγ, hn⟩ := exists_coeffNorm_eq Z.genMap (hG x)
    exact ⟨γ, hn.trans hx, hγ⟩
  -- `G = (1, 1)`: the boundary point `(1, 0)` maps to `1`, reached by `(1/2, 1/2)`
  · let Z : Zonotope (Vec ℝ 1) := ⟨2, 0, fun _ => ![1]⟩
    have hgen : ∀ β : Vec ℝ 2, Z.genMap β = ![β 0 + β 1] := by
      intro β; funext i; fin_cases i; simp [Z, Zonotope.genMap, Fin.sum_univ_two]
    refine ⟨Z, fun x => ⟨![x 0, 0], ?_⟩, ![1, 0], ?_, fun h => ?_⟩
    · rw [hgen]; funext i; fin_cases i; simp
    · refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_) ?_
      · fin_cases i <;> simp
      · simpa using norm_le_pi_norm (![1, 0] : Vec ℝ 2) 0
    · have hle : Z.zonotopeNorm (Z.genMap ![1, 0]) ≤ 1 / 2 := by
        have he : Z.genMap ![1, 0] = Z.genMap ![1 / 2, 1 / 2] := by
          rw [hgen, hgen]; funext i; fin_cases i; norm_num
        rw [Zonotope.zonotopeNorm, he]
        refine (coeffNorm_le _ _).trans ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_)
        fin_cases i <;> norm_num
      rw [h] at hle
      norm_num at hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
