module

public import CORALean.ContSet.Zonotope.Real.Operations.FaultResidual
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# No fault, no alarm

The fault test of [1, Eq. 31] declares "no fault" when `0 ∈ R_k` and "fault detected" when
`0 ∉ R_k`, `R_k` the residual zonotope of [1, Eq. 11] (`Zonotope.faultResidual`). What makes
the second verdict sound is that a fault-free output always passes: if `x` lies in the state
zonotope `X̂` and `y = C x + D_y v` with `v = H_v s`, `s` in the unit box [1, Eq. 5], then
`0 ∈ R`. With `x = p + θ`, `M(y - C p) = M C θ + M D_y H_v s`, so the coefficients `-β`, `-s`
reach `0`. A detected fault therefore means some output was not fault-free, given that every
state zonotope held its state, which [1, Eq. 10] gives only while no fault has occurred
(`LinearSysDT.faultObserve_outer`).

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n ny nv rv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.zero_mem_faultResidual (M : Mat ℝ ny ny) (C : Mat ℝ ny n)
    (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (X : Zonotope (Vec ℝ n)) (x : Vec ℝ n) (s : Vec ℝ rv)
    (hx : x ∈ X.construct) (hs : ∀ i, |s i| ≤ 1) :
    0 ∈ (X.faultResidual M C Dy Hv (C *ᵥ x + Dy *ᵥ (Hv *ᵥ s))).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  refine ⟨Fin.append (fun j => -β j) (fun j => -s j), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [hβ, hs]
  · show _ = _ + ∑ j : Fin (X.h + rv), _
    rw [Fin.sum_univ_add]
    simp only [Zonotope.faultResidual, Fin.append_left, Fin.append_right]
    -- the noise block is `-(M D_y H_v) s`, the state block `-M C θ`
    have hV : ∑ j, (-s j) • (fun i => (M * Dy * Hv) i j) = -((M * Dy * Hv) *ᵥ s) := by
      ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
    have hX : ∑ j, (-β j) • (M *ᵥ (C *ᵥ X.G j)) = -(M *ᵥ (C *ᵥ ∑ j, β j • X.G j)) := by
      simp only [neg_smul, Finset.sum_neg_distrib, mulVec_sum, mulVec_smul]
    rw [hV, hX]
    simp only [← mulVec_mulVec, mulVec_add, mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
