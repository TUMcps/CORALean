module

public import CORALean.Global.IpmBallEq

@[expose] public section

/-!
# The interval predictor of the example

[1, Sec. 2.3]: for the mechanism `y(ϕ) = ϕ(1 + |ϕ|)`, `ϕ ∈ [-1, 1]`, and the predictor
`I(ϕ) = {ϑϕ | ϑ ∈ [1, 2]}`, an instance of [1, Eq. 2]-[1, Eq. 4] (`c = 3/2`, `r = 1/2`, `γ = 0`),
[1, Eq. 6] gives `I(ϕ) = [1.5ϕ - 0.5|ϕ|, 1.5ϕ + 0.5|ϕ|]`, and `y(ϕ) ∈ I(ϕ)` for every `ϕ`, so the
predictor's reliability is 100% ([1, Def. 1]) whatever the distribution of `ϕ` on `[-1, 1]`.

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipmBall_example (ϕ : ℝ) (hϕ : |ϕ| ≤ 1) :
    ipmBall ![3 / 2] (1 / 2) 0 ![ϕ] = Set.Icc (3 / 2 * ϕ - 1 / 2 * |ϕ|) (3 / 2 * ϕ + 1 / 2 * |ϕ|) ∧
      ϕ * (1 + |ϕ|) ∈ ipmBall ![3 / 2] (1 / 2) 0 ![ϕ] := by -- --- PROOF ---
  have h : ipmBall ![3 / 2] (1 / 2) 0 ![ϕ] =
      Set.Icc (3 / 2 * ϕ - 1 / 2 * |ϕ|) (3 / 2 * ϕ + 1 / 2 * |ϕ|) := by
    rw [ipmBall_eq _ _ _ (by norm_num) le_rfl]
    have hs : Real.sqrt (![ϕ] ⬝ᵥ ![ϕ]) = |ϕ| := by
      rw [← Real.sqrt_sq_eq_abs]; congr 1; simp [dotProduct, sq]
    rw [hs]
    congr 1 <;> simp [dotProduct]
  refine ⟨h, ?_⟩
  rw [h]
  -- `ϕ(1 + |ϕ|) = ϑϕ` at `ϑ = 1 + |ϕ| ∈ [1, 2]`
  rcases le_or_gt 0 ϕ with h0 | h0
  · rw [abs_of_nonneg h0] at hϕ ⊢
    constructor <;> nlinarith
  · rw [abs_of_neg h0] at hϕ ⊢
    constructor <;> nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
