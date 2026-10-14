module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffOuterScalingCora

@[expose] public section

/-!
# CORA's `minkDiff(Z, I, 'outer:scaling')` is not an outer approximation

For the unit cube `Z = zonotope(zeros(3,1), eye(3))` and `I = interval(zeros(3,1), ones(3,1))`,
`Z ⊖ I = [-1, 0]³`. `'outer:scaling'` (`Zonotope.minkDiffOuterScalingCora`) scales `Z` by
`1 - 0.5/1 = 0.5` about its centre `0` and returns `[-0.5, 0.5]³`, ignoring `I`'s centre `0.5`:
the point `(-1, -1, -1)` of the difference is missing. `n = 3`, as at `n = 2` CORA forces
`'exact'`; `Z` is full-dimensional and `I` has generators, so no earlier branch returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffOuterScalingCora_not_outer :
    let Z : Zonotope (Vec ℝ 3) := ⟨3, 0, fun j i => if i = j then 1 else 0⟩
    let I : Interval (Vec ℝ 3) := ⟨0, 1⟩
    ¬ minkowskiDiff Z.construct I.construct ⊆
      (Z.minkDiffOuterScalingCora I).construct := by -- --- PROOF ---
  intro Z I h
  -- `(-1, -1, -1) + y ∈ Z` for every `y ∈ [0, 1]³`: coefficients `y - 1`
  have hmem : (fun _ => -1 : Vec ℝ 3) ∈ minkowskiDiff Z.construct I.construct := by
    intro y hy
    refine ⟨fun j => -1 + y j, fun j => ?_, ?_⟩
    · have hj : 0 ≤ y j ∧ y j ≤ 1 := hy j
      rw [abs_le]
      constructor <;> linarith [hj.1, hj.2]
    · funext i
      fin_cases i <;> simp [Z, Fin.sum_univ_three]
  -- the result is `[-0.5, 0.5]³`: coordinate `0` is `β₀ / 2 ≠ -1`
  obtain ⟨β, hβ, hx⟩ := h hmem
  have hof : ∀ f : Fin 3 → ℝ, (Entrywise.ofEntry f : Vec ℝ 3) = f := fun _ => rfl
  have hent : ∀ (f : Fin 3 → ℝ) (i : Fin 3), Entrywise.entry (f : Vec ℝ 3) i = f i :=
    fun _ _ => rfl
  have h0 := congrFun hx 0
  simp [Zonotope.minkDiffOuterScalingCora, Zonotope.interval, Interval.radius,
    Interval.zonotope, Fin.sum_univ_three, Z, I, hof, hent] at h0
  have hb := abs_le.mp (hβ (by exact (0 : Fin 3)))
  norm_num at h0
  linarith [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
