import CORALean.ContDynamics.NonlinearARX.Operations.SimulateBoxFloat
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateTrajectory
import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateMemSimulateBoxFloat

/-!
# The real windows lie in the float boxes

For a float model enclosing the converted system, the stacked window of the real `simulate`
from the real value of a float start window under the real value of a float input signal lies,
at every step, in the box `simulateBoxFloat` computes. An outer statement.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first window of the run is the start window. -/
theorem NonlinearARX.aux_stack_simulate_zero (sys : NonlinearARX dy du p) (y₀ : Vec ℝ (p * dy))
    (u : ℕ → Vec ℝ du) :
    NonlinearARX.stack p (sys.simulate y₀ u) 0 = y₀ := by -- --- PROOF ---
  funext r
  have hlt : (0 + (finProdFinEquiv.symm r).1 : ℕ) < p := by
    simpa using (finProdFinEquiv.symm r).1.isLt
  have hs : sys.simulate y₀ u (0 + (finProdFinEquiv.symm r).1 : ℕ)
      = fun b => y₀ (finProdFinEquiv (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, b)) := by
    rw [NonlinearARX.simulate, dif_pos hlt]
  show sys.simulate y₀ u (0 + (finProdFinEquiv.symm r).1 : ℕ) (finProdFinEquiv.symm r).2 = _
  rw [hs]
  have hf : (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, (finProdFinEquiv.symm r).2)
      = finProdFinEquiv.symm r := Prod.ext (Fin.ext (zero_add _)) rfl
  show y₀ (finProdFinEquiv (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, _)) = _
  rw [hf, Equiv.apply_symm_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.simulate_mem_simulateBoxFloat (sys : NonlinearARX dy du p)
    {fm : NonlinearSysDT.FloatModel 𝕋 (p * dy) ((p + 1) * du)}
    (h : fm.Encloses sys.toNonlinearSysDT) (y₀ : Vec 𝕋 (p * dy)) (u : ℕ → Vec 𝕋 du) (k : ℕ) :
    NonlinearARX.stack p (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k ∈
      construct (sys.simulateBoxFloat fm y₀ u k) := by -- --- PROOF ---
  -- the ARX recursion for `k ≥ p` is `simulate`'s definition
  have hrec : ∀ k, p ≤ k →
      sys.simulate (Scalar.toRealVec y₀) (fun j => Scalar.toRealVec (u j)) k
        = sys.f (NonlinearARX.pastOut p
            (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k)
          (NonlinearARX.pastIn p (fun j => Scalar.toRealVec (u j)) k) :=
    fun k hk => by rw [NonlinearARX.simulate, dif_neg (not_lt.mpr hk)]; rfl
  induction k with
  | zero =>
    rw [sys.aux_stack_simulate_zero]
    exact Interval.mem_point y₀
  | succ k ih =>
    rw [sys.toNonlinearSysDT_step hrec k]
    exact h.f_mem _ _ _ ih _ (Interval.mem_point (NonlinearARX.feed p u k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
