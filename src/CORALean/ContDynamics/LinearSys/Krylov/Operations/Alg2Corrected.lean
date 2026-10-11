import CORALean.Global.Tensor
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Alg. 2, with lines 8 and 10 repaired

[1, Alg. 2] (Compute `R([0, t_f])`) with two lines repaired, otherwise as `Alg2` has it. Line 8
propagates `R*_{b,1}` by `e^{Akδ}`, (24)'s `e^{At_k}` at `t_k = kδ`, not by the printed
`e^{A(k+1)δ}`, which skips a step (`printed_input_propagation_counterexample`). Line 10 gives
`theorem_III.2` the end set `theorem_III.1(R*_{h,k}, A, δ)` of its own start set `R*_{h,k}`, as
`Thm. III.2` is stated and proved (`timeInterval_subset`), not the `R*_{h,k+1}` computed from
`X₀`. Line 2 is whatever encloses `R_p(δ)`; `Cor. IV.2` as printed does not
(`varying_input_reach_counterexample`), its corrected form does
(`inputReach_subset_krylovZonotope`).

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] with `e^{Akδ}` in line 8 and `theorem_III.2` given its own end set in line 10. -/
def Krylov.alg2Corrected (theoremIII1 : Set (Vec ℝ n) → ℝ → Set (Vec ℝ n))
    (corollaryIV2 : Set (Vec ℝ n)) (theoremIII2 : Set (Vec ℝ n) → Set (Vec ℝ n) → Set (Vec ℝ n))
    (X₀ : Set (Vec ℝ n)) (δ tf : ℝ) : Set (Vec ℝ n) :=
  let box : Set (Vec ℝ n) → Set (Vec ℝ n) :=
    fun S => {x | ∀ i, ∃ y ∈ S, ∃ z ∈ S, y i ≤ x i ∧ x i ≤ z i}
  let Rsh1 := theoremIII1 X₀ δ                              -- line 1
  let Rsb1 := corollaryIV2                                  -- line 2
  let Rp1 := box (convexHull ℝ (insert 0 Rsb1))             -- line 3
  let Rh1 := theoremIII2 X₀ Rsh1                            -- line 4
  let R1 := Rh1 + Rp1                                       -- line 5
  -- lines 6–12: `(R*_{h,k}, R_{p,k}, R_k)` after the pass for `k = m`, `m + 1` its index
  let state : ℕ → Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n) := fun m =>
    Nat.rec (motive := fun _ => Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n)) (Rsh1, Rp1, R1)
      (fun m prev =>
        let k : ℝ := m + 1
        let Rshk1 := theoremIII1 X₀ ((k + 1) * δ)           -- line 7
        let Rsbk1 := theoremIII1 Rsb1 (k * δ)               -- line 8
        let Rpk1 := prev.2.1 + box Rsbk1                    -- line 9
        let Rhk1 := theoremIII2 prev.1 (theoremIII1 prev.1 δ)  -- line 10
        let Rk1 := Rhk1 + Rpk1                              -- line 11
        (Rshk1, Rpk1, Rk1)) m
  ⋃ m ∈ Finset.range ⌈tf / δ⌉₊, (state m).2.2               -- line 13

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
