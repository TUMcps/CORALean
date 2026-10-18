module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerTerm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Every Peano–Baker term is continuous in time

Entry by entry. The base term is constant; each later one is a primitive of
`A(σ) P_k(σ)`, an integrable entry of `A` against a continuous one of `P_k`, and
a primitive of a locally integrable function is continuous. Nothing is asked of
`A` beyond integrability of its entries over every bounded window.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Continuity and the integrability of the next integrand, carried together
since each needs the other one order down. -/
theorem aux_continuous_and_integrable {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) (k : ℕ) : -- --- STMT ---
    (∀ i j, Continuous fun s => MatExp.peanoBakerTerm A k s i j) ∧
    (∀ i j a b, IntervalIntegrable
      (fun σ => (A σ * MatExp.peanoBakerTerm A k σ) i j) volume a b) := by -- --- PROOF ---
  induction k with
  | zero =>
    refine ⟨fun i j => continuous_const, fun i j a b => ?_⟩
    simp only [MatExp.peanoBakerTerm, mul_one]
    exact hA i j a b
  | succ k ih =>
    -- a primitive of a locally integrable function is continuous
    have hc : ∀ i j, Continuous fun s => MatExp.peanoBakerTerm A (k + 1) s i j := fun i j =>
      intervalIntegral.continuous_primitive (fun a b => ih.2 i j a b) 0
    refine ⟨hc, fun i j a b => ?_⟩
    simp only [Matrix.mul_apply]
    have h := IntervalIntegrable.sum Finset.univ fun l _ =>
      (hA i l a b).mul_continuousOn (hc l j).continuousOn
    rwa [Finset.sum_fn] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each entry of each term is continuous, given integrable entries of `A`. -/
theorem MatExp.continuous_peanoBakerTerm {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) (k : ℕ) (i j : Fin n) :
    Continuous fun s => MatExp.peanoBakerTerm A k s i j :=
  (aux_continuous_and_integrable hA k).1 i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
