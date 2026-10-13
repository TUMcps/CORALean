module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundAtTop
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

/-!
# Any admissible error is reachable, in the order

[1]: the ε-form of `tendsto_expRemainderBound_atTop`, and the statement
adaptive order selection actually calls: for every admissible error there is
an order whose bound beats it, and whose side condition `‖x‖/(η+2) < 1` also
holds, so the `η` produced names a real bound rather than a divergent one.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The order the tuning algorithm actually needs to name: a real bound under
`ε`, sound because its own side condition holds too. -/
theorem MatExp.exists_expRemainderBound_lt (x : Mat ℝ n n) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℕ, MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1 := by -- --- PROOF ---
  have hev1 : ∀ᶠ η : ℕ in atTop, MatExp.expRemainderBound x η < ε :=
    (MatExp.tendsto_expRemainderBound_atTop x).eventually_lt_const hε
  have hden : Tendsto (fun η : ℕ => (η : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hT2 : Tendsto (fun η : ℕ => ‖x‖ / ((η : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hev2 : ∀ᶠ η : ℕ in atTop, ‖x‖ / ((η : ℝ) + 2) < 1 := hT2.eventually_lt_const one_pos
  exact (hev1.and hev2).exists

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
