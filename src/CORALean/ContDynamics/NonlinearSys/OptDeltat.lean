import CORALean.Global.Tensor

/-!
# `optDeltat`: the time step size that balances the two wrapping effects

Line 10 of [1, Alg. 2], which is its §5.4, and lines 8 and 12 of [2, Alg. 2],
whose (30) and (31) are eq. (57) and eq. (58) here: over a finite horizon `h`
walked in `λ = ζ_δ^{-λ'}` steps, (57) estimates the size the start set reaches
and (58) minimizes it over `λ'`. Too large a step makes the set of abstraction
errors large, too small a step reduces too often; the minimum is the balance.

Scalars throughout, which is [1]'s own simplification: `r₀` and `r_abs` are the
radii of `R(t)` and of `R_abs(h)`, and `ζ_A = e^{tr(Ah)}` is eq. (50)'s
determinant estimate. Nothing here is a set.

`λ` is the lambda binder, so eq. (57)'s `λ` is `lam` and its `λ'` is `scalings`.

`λ'` is searched by increasing it while the estimate falls, as [1] says to do
— no `Nat.find` and no `Classical.choose`, every decision going through the
caller's `le`, and `fuel` bounding a loop with no stated iteration count.
`λ'_*` comes back beside `Δt*`: line 16's `estimateGain` needs it.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

/-- `φ(j+1)` of eq. (54): the gain interpolated between `φ⁽¹⁾` at the horizon
and the limit gain `ζ_δ`. -/
noncomputable def interpGain (ζδ φ1 : ℝ) (j : ℕ) : ℝ :=
  ζδ + (φ1 - ζδ) * ζδ ^ j

/-- Eq. (57): the size `R(t)` is estimated to reach after the finite horizon,
walked in `λ = ζ_δ^{-λ'}` steps. -/
noncomputable def reachSizeEstimate (ζδ ζZ ζA φ1 r₀ rabs : ℝ) (scalings : ℕ) : ℝ :=
  let lam := (1 / ζδ) ^ scalings                                -- λ = ζ_δ^{-λ'}
  let N := ⌊lam⌋₊                                               -- ⌊λ⌋ whole steps
  let b := lam - (N : ℝ)                                        -- the last incomplete step
  let ζAZ := (∑ j ∈ Finset.Icc 1 N,                             -- 53. ζ_{A,Z}(λ)
      (1 + 2 * ζZ) ^ (b + (j : ℝ)) * ζA ^ ((b + (j : ℝ) - 1) / lam))
    + b * (1 + 2 * ζZ) ^ b
  r₀ * (1 + 2 * ζZ) ^ lam * ζA                                  -- 57. the start set, propagated
    + rabs / lam * ζAZ * ∏ j ∈ Finset.range scalings, interpGain ζδ φ1 j -- 57. errors, accumulated

/-- Increase `λ'` while the estimate keeps falling, and stop at the first
increase — [1]'s own evaluation of eq. (58). -/
noncomputable def optDeltatSearch (le : ℝ → ℝ → Bool) (cost : ℕ → ℝ) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, k + 1 => if le (cost (s + 1)) (cost s) then optDeltatSearch le cost (s + 1) k else s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
noncomputable def optDeltat (le : ℝ → ℝ → Bool) (ζδ ζZ ζA φ1 r₀ rabs h : ℝ) (fuel : ℕ) :
    ℝ × ℕ :=
  let cost := reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs             -- 57. the cost function
  let sstar := optDeltatSearch le cost 0 fuel                    -- 58. the argmin over λ'
  (h * ζδ ^ sstar, sstar)                                        -- 58. Δt* = h ζ_δ^{λ'}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
