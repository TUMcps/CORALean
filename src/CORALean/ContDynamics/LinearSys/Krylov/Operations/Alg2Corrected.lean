module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

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

## Inputs
* `theoremIII1` – subroutine enclosing the matrix-exponential image
* `corollaryIV2` – input solution enclosure
* `theoremIII2` – subroutine for the homogeneous step solution
* `X₀` – initial set
* `δ` – step length
* `tf` – final time

## Output
* union of the repaired step sets over the time horizon

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov
      Subspace". IEEE Transactions on Automatic Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


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
  -- 1. R*_{h,1} ← theorem_III.1(X₀, A, δ)
  let Rsh1 := theoremIII1 X₀ δ
  -- 2. R*_{b,1} ← corollary_IV.2(U, A, B, δ)
  let Rsb1 := corollaryIV2
  -- 3. R_{p,1} ← box(conv(0, R*_{b,1}))
  let Rp1 := box (convexHull ℝ (insert 0 Rsb1))
  -- 4. R_{h,1} ← theorem_III.2(X₀, R*_{h,1}, A, δ)
  let Rh1 := theoremIII2 X₀ Rsh1
  -- 5. R_1 ← R_{h,1} ⊕ R_{p,1}
  let R1 := Rh1 + Rp1
  -- 6.-12. for k = 1 … ⌈t_f/δ - 1⌉: `(R*_{h,k}, R_{p,k}, R_k)` after `m` passes, `k = m + 1`
  let state : ℕ → Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n) := fun m =>
    Nat.rec (motive := fun _ => Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n)) (Rsh1, Rp1, R1)
      (fun m prev =>
        let k : ℝ := m + 1
        -- 7. R*_{h,k+1} ← theorem_III.1(X₀, A, (k + 1)δ)
        let Rshk1 := theoremIII1 X₀ ((k + 1) * δ)
        -- 8. R*_{b,k+1} ← theorem_III.1(R*_{b,1}, A, kδ), with `e^{Akδ}`
        let Rsbk1 := theoremIII1 Rsb1 (k * δ)
        -- 9. R_{p,k+1} ← R_{p,k} ⊕ box(R*_{b,k+1})
        let Rpk1 := prev.2.1 + box Rsbk1
        -- 10. R_{h,k+1} ← theorem_III.2(R*_{h,k}, theorem_III.1(R*_{h,k}, A, δ), A, δ)
        let Rhk1 := theoremIII2 prev.1 (theoremIII1 prev.1 δ)
        -- 11. R_{k+1} ← R_{h,k+1} ⊕ R_{p,k+1}
        let Rk1 := Rhk1 + Rpk1
        (Rshk1, Rpk1, Rk1)) m
  -- 13. R([0, t_f]) ← ⋃_k R_k
  ⋃ m ∈ Finset.range ⌈tf / δ⌉₊, (state m).2.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
