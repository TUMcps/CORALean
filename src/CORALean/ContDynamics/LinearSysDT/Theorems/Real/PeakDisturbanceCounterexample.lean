module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section

/-!
# The peak of a disturbance is not the worst case of its set

[1, Remark 1], its Eq. 3: for `d_k ∈ D = ⟨0, H_d⟩`, `‖d‖_∞ = sup_k ‖d_k‖ = max_{b ∈ B} ‖H_d b‖`.
The first expression depends on the sequence, the second does not: at `H_d = 1` in one dimension
the admissible run `d ≡ 0` has `sup_k ‖d_k‖ = 0`, while `max_{|b| ≤ 1} |b| = 1`. Only
`sup_k ‖d_k‖ ≤ max_b ‖H_d b‖` holds (`LinearSysDT.peakDisturbance_le`).

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.peakDisturbance_counterexample :
    let Hd : Mat ℝ 1 1 := 1
    let d : ℕ → Vec ℝ 1 := fun _ => 0
    (∀ k, ∃ b : Vec ℝ 1, (∀ i, |b i| ≤ 1) ∧ d k = Hd *ᵥ b) ∧
      (⨆ k, Real.sqrt (d k ⬝ᵥ d k)) ≠
        sSup ((fun b : Vec ℝ 1 => Real.sqrt ((Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b))) ''
          {b | ∀ i, |b i| ≤ 1}) := by -- --- PROOF ---
  intro Hd d
  refine ⟨fun k => ⟨0, fun _ => by simp, by simp [d]⟩, ?_⟩
  -- the box term is `1`, attained at `b = 1`
  have hbox : sSup ((fun b : Vec ℝ 1 => Real.sqrt ((Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b))) ''
      {b | ∀ i, |b i| ≤ 1}) = 1 := by
    refine IsGreatest.csSup_eq ⟨⟨fun _ => 1, fun _ => by simp, by simp [Hd, dotProduct]⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have h := abs_le.mp (hb 0)
    simp only [Hd, one_mulVec, dotProduct, Fin.sum_univ_one]
    rw [Real.sqrt_le_one]
    nlinarith [h.1, h.2]
  rw [hbox]
  simp [d]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
