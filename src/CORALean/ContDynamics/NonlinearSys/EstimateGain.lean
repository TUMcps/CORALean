import CORALean.ContDynamics.NonlinearSys.OptDeltat

/-!
# `estimateGain`: the gain at the finite horizon, read back from two radii

Line 16 of [1, Alg. 2]: eq. (56) fixes `φ⁽¹⁾` implicitly, by asking the product
`φ(1)·…·φ(λ')` of eq. (54)'s interpolated gains to equal `λ r⁽ᵛ⁾_abs / r⁽¹⁾_abs`
— the two radii the step's two passes just computed. [1] calls solving it
`estimateGain` and says nothing about how.

How, here, is bisection on `[0,1]`: every factor of the left-hand side grows
with `φ⁽¹⁾`, so the product does, and halving the bracket toward the crossing
converges to the solution. A gain is a ratio of two widths, so `[0,1]` is where
the answer is and the bracket needs no search of its own.

No `Nat.find` and no `Classical.choose`: every decision goes through the
caller's `le`, in the style of `Global/Float/Log.lean`, so a float layer
transcribes this and it runs. `fuel` is the number of halvings, and the
accompanying theorem is what it buys.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

/-- Halve the bracket toward where `g` crosses `target`, `fuel` times, and hand
back the last midpoint. -/
noncomputable def estimateGainSearch (le : ℝ → ℝ → Bool) (g : ℝ → ℝ) (target : ℝ) :
    ℝ → ℝ → ℕ → ℝ
  | lo, hi, 0 => (lo + hi) / 2
  | lo, hi, k + 1 =>
    let mid := (lo + hi) / 2
    if le (g mid) target then estimateGainSearch le g target mid hi k
    else estimateGainSearch le g target lo mid k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 16: the gain `φ⁽¹⁾` eq. (56) fixes, at the `λ'` the step
size search settled on. -/
noncomputable def estimateGain (le : ℝ → ℝ → Bool) (ζδ lam rabs1 rabsOpt : ℝ)
    (scalings fuel : ℕ) : ℝ :=
  let target := lam * rabsOpt / rabs1                          -- 56. the right-hand side
  let lhs := fun φ1 => ∏ j ∈ Finset.range scalings,            -- 56. the left-hand side
    interpGain ζδ φ1 j
  estimateGainSearch le lhs target 0 1 fuel                    -- 56. solve for φ⁽¹⁾ in [0,1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
