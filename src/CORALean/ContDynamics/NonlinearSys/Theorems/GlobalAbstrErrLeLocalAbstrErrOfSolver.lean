module

public import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrLeLocalAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrStepOfSolver
public import Mathlib.Topology.GDelta.MetrizableSpace

@[expose] public section

/-!
# `[1, Lemma 2]` outright, for a solver of the form (10) at a fixed `A`

Composes `globalAbstrErr_succ_le_of_solver` — (10)'s recursion, expanded into `hstep` — with
`globalAbstrErr_le_of_localAbstrErr`, the discrete Grönwall step [1]'s own proof defers to a
cited textbook. Nothing here is assumed: the per-step bound is proved from (B.1)-(B.2). `A` is
one fixed matrix, not a per-step `A_k`, as (B.1)-(B.2) already read in [1]'s Appendix B; a
re-linearizing run is out of scope. `hA : A ≠ 0` keeps the accumulation constant `L` positive,
which `aux_gronwall` needs to divide by.

## Inputs
* `A` – state matrix
* `Δt` – step size
* `tEnd` – final time
* `N` – number of steps
* `R` – runs with error
* `Rhat` – error-free runs
* `Rabs` – abstraction error sets
* `P` – particular-solution sets

## Hypotheses
* `hA` – matrix nonzero
* `hΔt` – step size positive
* `hN` – step count positive
* `htEnd` – final time is steps times size
* `hR0` – initial runs agree
* `hB1` – run with error follows recursion
* `hB2` – error-free run follows recursion
* `hRhatNe` – error-free runs nonempty
* `hRhatBdd` – error-free runs bounded
* `hRabsNe` – error sets nonempty
* `hRabsConv` – error sets convex
* `hRabsCpt` – error sets compact

## Conclusion
* the final global error is at most the scaled worst local error

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A set measured against itself carries no error at all. -/
theorem aux_globalAbstrErr_self {X : Set (Vec ℝ n)} (hne : X.Nonempty)
    (hb : Bornology.IsBounded X) : globalAbstrErr X X = 0 := by -- --- PROOF ---
  have hXz : X + ({0} : Set (Vec ℝ n)) = X := by simp
  have h := globalAbstrErr_eq_localAbstrErr (Rhat := X) (Rabs := ({0} : Set (Vec ℝ n))) hne hb
    (convex_singleton 0) isClosed_singleton
  rw [hXz] at h
  rw [h, localAbstrErr]
  have hd : boxDiameter ({0} : Set (Vec ℝ n)) = 0 := by
    funext i
    show sSup ((fun x : Vec ℝ n => x i) '' ({0} : Set (Vec ℝ n))) -
      sInf ((fun x : Vec ℝ n => x i) '' ({0} : Set (Vec ℝ n))) = 0
    rw [Set.image_singleton, csSup_singleton, csInf_singleton, sub_self]
  rw [hd, norm_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Lemma 2]`, outright: for a solver of the form (10) at one fixed linearization
matrix `A ≠ 0`, the global error after `N` equal steps is at most the worst local error
over the run, scaled by a constant depending on `t_end` alone. -/
theorem globalAbstrErr_le_of_localAbstrErr_of_solver {A : Mat ℝ n n} (hA : A ≠ 0) {Δt tEnd : ℝ}
    (hΔt : 0 < Δt) {N : ℕ} (hN : 0 < N) (htEnd : (N : ℝ) * Δt = tEnd)
    {R Rhat Rabs P : ℕ → Set (Vec ℝ n)} (hR0 : R 0 = Rhat 0)
    (hB1 : ∀ k < N, R (k + 1) = (exp (Δt • A)).mulVec '' R k + P k + Rabs k)
    (hB2 : ∀ k < N, Rhat (k + 1) = (exp (Δt • A)).mulVec '' Rhat k + P k)
    (hRhatNe : ∀ k ≤ N, (Rhat k).Nonempty) (hRhatBdd : ∀ k ≤ N, Bornology.IsBounded (Rhat k))
    (hRabsNe : ∀ k < N, (Rabs k).Nonempty) (hRabsConv : ∀ k < N, Convex ℝ (Rabs k))
    (hRabsCpt : ∀ k < N, IsCompact (Rabs k)) : -- --- CONCL ---
    globalAbstrErr (R N) (Rhat N) ≤
      (Real.exp (‖A‖ * Real.exp (tEnd * ‖A‖) * tEnd) - 1) / (‖A‖ * Real.exp (tEnd * ‖A‖)) / Δt *
      (Finset.range N).sup' (Finset.nonempty_range_iff.mpr hN.ne')
        (fun k => localAbstrErr (Rabs k)) := by -- --- PROOF ---
  have hLpos : 0 < ‖A‖ * Real.exp (tEnd * ‖A‖) :=
    mul_pos (norm_pos_iff.mpr hA) (Real.exp_pos _)
  have hzero : globalAbstrErr (R 0) (Rhat 0) = 0 := by
    rw [hR0]; exact aux_globalAbstrErr_self (hRhatNe 0 hN.le) (hRhatBdd 0 hN.le)
  have hΔtEnd : Δt ≤ tEnd := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [hΔt.le]
  exact globalAbstrErr_le_of_localAbstrErr R Rhat Rabs hLpos hΔt hN htEnd hzero
    (fun k hk => globalAbstrErr_succ_le_of_solver hΔt hΔtEnd hR0 hB1 hB2
      hRhatNe hRhatBdd hRabsNe hRabsConv hRabsCpt hk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
