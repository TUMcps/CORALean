module

public import CORALean.ContSet.Interval.Real.Operations.Center
public import CORALean.ContSet.Interval.Real.Operations.EnclosePoints
public import CORALean.ContSet.Interval.Real.Operations.Radius
public import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotopeCompress
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# The loop of `Zonotope.cloud2zonotope`

[1, Alg. 3, steps 2-11]: centre the cloud on its interval hull, find its first principal direction
`u`, cut a generator `g = ratio |u · rad| u`, compress the cloud along `g` and add the segment
`[-1, 1] g` to the zonotope. `minbox` is `Interval.enclosePoints`, `(mid, rad)` its centre and
radius, and `svd(X)(:, 1)` is the argument `dir`, which has no algorithm here. The zonotope
`c ⊕ Z(R)` is carried as a `Zonotope`, `c := c + mid, R := [R, g]` being one Minkowski sum with
`⟨mid, g⟩`. The fuel `k` is `s₁ - iter`.

The loop test is read as the text states it, "until one of the two stopping criteria `s₁` or `s₂`
is satisfied": continue while `iter < s₁` and some `radᵢ > s₂ wᵢ` (the printed `∨` would run on
until both are met). The first pass is unconditional: `rad` is unassigned when the test is first
made, and `w = 0`.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {κ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `while` loop of `cloud2zonotope`: returns the zonotope `c ⊕ Z(R)` built and the residual
cloud `X`. -/
noncomputable def Zonotope.cloud2zonotopeLoop [Fintype κ] [Nonempty κ]
    (dir : (κ → Vec ℝ n) → Vec ℝ n) (ratio s₂ : ℝ) :
    ℕ → ℕ → Vec ℝ n → Zonotope (Vec ℝ n) → (κ → Vec ℝ n) →
      Zonotope (Vec ℝ n) × (κ → Vec ℝ n)
  | 0, _, _, Z, X => (Z, X)
  | k + 1, iter, w, Z, X =>
    let iter := iter + 1
    let I := Interval.enclosePoints X
    let mid := I.center
    let rad := I.radius
    let X := fun j => X j - mid
    let w := if iter = 1 then rad else w
    let u := dir X
    let g := (ratio * |u ⬝ᵥ rad|) • u
    let X := Zonotope.cloud2zonotopeCompress X g
    let Z := Z.plus ⟨1, mid, fun _ => g⟩
    open Classical in
    if ∃ i, s₂ * w i < rad i then
      Zonotope.cloud2zonotopeLoop dir ratio s₂ k iter w Z X
    else (Z, X)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
