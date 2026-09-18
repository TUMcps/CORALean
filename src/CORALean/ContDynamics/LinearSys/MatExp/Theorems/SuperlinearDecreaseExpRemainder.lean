import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundSuperlinear
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.Global.SuperlinearDecrease

/-!
# `Lemma 1`: the exponential remainder decreases superlinearly

[1, Lemma 1]: `∀φ∈(0,1): E(φΔt,η) ⊆ φ·E(Δt,η)`, `E` being `MatExp.expRemainder`
— an entrywise-uniform box, so a member of the smaller one scaled back up by
`φ⁻¹` is a member of the larger, and `expRemainderBound_superlinear` is exactly
what keeps it inside.

Stated at `construct`, the interval matrix as a set, which is what `Def. 1`
quantifies over; `SuperlinearDecrease` is satisfied literally, with `E`'s own
`Δt` filling `Def. 1`'s length argument.

`hΔt`, the side condition at `Δt` alone, is the hypothesis `Enclosures.lean`
already carries — `φ < 1` is what sends it down to `φΔt` inside the proof, so
nothing further is asked of the caller there.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: the remainder's box shrinks by at least `φ` when the step
does, at every order `η` and every `Δt` meeting the usual side condition. -/
theorem MatExp.superlinearDecrease_expRemainder {A : Mat ℝ n n} {Δt : ℝ} (η : ℕ)
    (hΔt : ‖Δt • A‖ / ((η : ℝ) + 2) < 1) :
    SuperlinearDecrease (fun δ => (MatExp.expRemainder A δ η).construct) Δt := by -- --- PROOF ---
  intro φ hφ M hM
  obtain ⟨hφ0, hφ1⟩ := hφ
  have hbound : MatExp.expRemainderBound ((φ * Δt) • A) η
      ≤ φ * MatExp.expRemainderBound (Δt • A) η := by
    rw [mul_smul]
    exact MatExp.expRemainderBound_superlinear η hφ0 hφ1 hΔt
  have hstep : φ⁻¹ * MatExp.expRemainderBound ((φ * Δt) • A) η
      ≤ MatExp.expRemainderBound (Δt • A) η := by
    have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hφ0.le)
    rwa [inv_mul_cancel_left₀ hφ0.ne'] at h
  -- the witness scaling `M` back up: `φ • (φ⁻¹ • M) = M` puts it back where it started
  refine Set.mem_smul_set.mpr ⟨φ⁻¹ • M, Interval.mem_mat_iff.mpr fun i j => ?_, ?_⟩
  · have hMij := Interval.mem_mat_iff.mp hM i j
    simp only [MatExp.expRemainder] at hMij
    have habs : |M i j| ≤ MatExp.expRemainderBound ((φ * Δt) • A) η := abs_le.mpr hMij
    have hentry : (φ⁻¹ • M) i j = φ⁻¹ * M i j := rfl
    have hbnd : |(φ⁻¹ • M) i j| ≤ MatExp.expRemainderBound (Δt • A) η := by
      rw [hentry, abs_mul, abs_of_pos (inv_pos.mpr hφ0)]
      calc φ⁻¹ * |M i j| ≤ φ⁻¹ * MatExp.expRemainderBound ((φ * Δt) • A) η :=
            mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hφ0.le)
        _ ≤ MatExp.expRemainderBound (Δt • A) η := hstep
    simpa only [MatExp.expRemainder] using abs_le.mp hbnd
  · rw [smul_smul, mul_inv_cancel₀ hφ0.ne', one_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
