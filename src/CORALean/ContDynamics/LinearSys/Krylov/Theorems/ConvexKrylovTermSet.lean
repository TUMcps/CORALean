module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentArnoldiPow
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# The Krylov Taylor sets are convex below the Krylov order

The merge (29) in [1]'s proof of [1, Thm. IV.2] (Appendix A), `aD ⊕ bD = (a + b)D`, holds for
a convex `D`, and is applied to `P D⁽ʲ⁾ e₁ = {P Ṽ(u) H̃ʲ(u) e₁ / j! | u ∈ U}`. Nothing in [1]
says this set is convex: `Ṽ(u)` and `H̃(u)` depend on `u` through the Arnoldi iteration. Below
the Krylov order it is: `P Ṽ(u) H̃ʲ(u) e₁ = A^{j-1} u` (`augment_arnoldi_pow`), so the set is
the linear image `A^{j-1} U / j!` of the convex `U`. At and above the order `ξ` the identity,
and with it the argument, is gone.

## Inputs
* `A` – system matrix
* `U` – input set
* `m` – Krylov order
* `j` – power

## Hypotheses
* `hU` – input set convex
* `hj1` – power at least one
* `hj` – power at most the Krylov order

## Conclusion
* the set of Krylov Taylor terms is convex

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P D⁽ʲ⁾ e₁ = {P Ṽ(u) H̃ʲ(u) e₁ / j! | u ∈ U}` is convex for `1 ≤ j ≤ m`, `ξ = m + 1`. -/
theorem Krylov.convex_krylovTermSet (A : Mat ℝ n n) {U : Set (Vec ℝ n)} (hU : Convex ℝ U)
    (m : ℕ) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m) : -- --- CONCL ---
    Convex ℝ ((fun u : Vec ℝ n => ((Nat.factorial j : ℝ))⁻¹ • fun i =>
        (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
          (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) ^ j
            *ᵥ Pi.single 0 1)) (Fin.castSucc i)) '' U) := by -- --- PROOF ---
  -- the set is the image of `U` under the linear map `u ↦ A^{j-1} u / j!`
  have himg : (fun u : Vec ℝ n => ((Nat.factorial j : ℝ))⁻¹ • fun i =>
        (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
          (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) ^ j
            *ᵥ Pi.single 0 1)) (Fin.castSucc i)) '' U
      = Matrix.mulVecLin (((Nat.factorial j : ℝ))⁻¹ • A ^ (j - 1)) '' U := by
    refine Set.image_congr fun u _ => ?_
    rw [Krylov.augment_arnoldi_pow A u m hj1 hj, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  rw [himg]
  exact hU.linear_image _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
