import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsFeasibleIffIsLeast

/-!
# Membership by one linear program

[1, Prop. 2, eq. 20]: `z ∈ Z` iff `min{‖ξ‖∞ : [G; A]ξ = [z − c; b]} ≤ 1`. The stacked system is
`Matrix.fromRows`, indexed by a sum type, with the generators as the first block of columns
of `G`; `Z` and the minimum are as in `nonempty_iff_isLeast`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2, eq. 20]: `z ∈ Z` iff the minimum of `‖ξ‖∞` over `[G; A]ξ = [z − c; b]`
exists and is `≤ 1`. -/
theorem ConZonotope.mem_iff_isLeast {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (z : Vec ℝ n) :
    z ∈ (ConZonotope.ofMat c G A b).construct ↔
      ∃ m, IsLeast {t | ∃ ξ : Vec ℝ h,
        Matrix.fromRows (Matrix.of fun (i : Fin n) (j : Fin h) => G j i) A *ᵥ ξ
          = Sum.elim (z - c) b ∧ t = ‖ξ‖} m ∧ m ≤ 1 := by -- --- PROOF ---
  rw [← ConZonotope.exists_feasible_iff_isLeast]
  simp only [Matrix.fromRows_mulVec]
  constructor
  · intro hz
    obtain ⟨β, hβ, hAβ, hx⟩ := ConZonotope.mem_ofMat_iff.mp hz
    refine ⟨β, funext fun s => ?_, hβ⟩
    -- first block: the generators give `z − c`, second: `Aβ = b`
    rcases s with i | i
    · have := congrFun hx i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] at this ⊢
      linarith
    · exact hAβ i
  · rintro ⟨β, hβ, hbox⟩
    refine ConZonotope.mem_ofMat_iff.mpr ⟨β, hbox, fun i => congrFun hβ (Sum.inr i), ?_⟩
    funext i
    have := congrFun hβ (Sum.inl i)
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] at this ⊢
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
