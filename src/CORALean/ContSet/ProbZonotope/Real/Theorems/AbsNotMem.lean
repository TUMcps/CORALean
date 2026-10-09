import CORALean.ContSet.ProbZonotope.Real.Operations.Abs

/-!
# `ProbZonotope.abs` does not enclose the absolute values of the means

The mean zonotope with generators `(1, 1)` and `(1, -1)` contains `(2, 0)`, whose entrywise absolute
value is not in `abs` of it, which is the segment `{(t, t)}`: `abs` takes the entrywise absolute
value of `[c, G]`, a different set and not an enclosure (`AbsLeCorner` is what it keeps).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.abs_not_mem :
    ∃ (P : ProbZonotope 2) (μ : Vec ℝ 2), μ ∈ P.Z.construct ∧
      (fun i => |μ i|) ∉ P.abs.Z.construct := by -- --- PROOF ---
  -- the means `g₁ + g₂ = (2, 0)` of the zonotope `⟨0, (1, 1), (1, -1)⟩`
  refine ⟨⟨⟨2, 0, ![![1, 1], ![1, -1]]⟩, 0⟩, ![2, 0], ⟨![1, 1], ?_, ?_⟩, ?_⟩
  · intro j; fin_cases j <;> simp
  · funext i
    fin_cases i
    · simp [Fin.sum_univ_two]; norm_num
    · simp [Fin.sum_univ_two]
  -- no coefficients put `(2, 0)` on the segment: the two coordinates would be equal
  · rintro ⟨β, -, h⟩
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [ProbZonotope.abs, Zonotope.abs] at h0 h1
    erw [Fin.sum_univ_two] at h0 h1
    simp at h0 h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
