module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportRadius
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# One step of the bounded-error identification algorithm

[1, Sec. 3.3], steps 2 to 5, for the zonotope `AFSS_k = X`, the measurement `(y, r)` with bound `σ`
and the expansion `γ`: the tight strip is the support strip of `X` met with `|rᵀθ - y| ≤ σ` ([1,
Def. 9]), written as `|rᵀθ - d| ≤ σ'` with center `d` and half-width `σ'` (the paper does not say
how, and takes the strip as given); `intersectStrip` at the gain `λ` gives `X̂(λ) = p̂(λ) ⊕ Ĥ(λ)
Bʳ⁺¹` ([1, Property 1]), and `AFSS_{k+1} = X̂(λ) ⊕ diag(γ) Bⁿ`. The gain `λ` is an argument: the
paper chooses `λ*` to minimise the volume, and the enclosure holds for every `λ`. The expansion `γ`
is a vector, one bound per parameter, as in the paper's example.

## Inputs
* `X` – parameter zonotope
* `r` – regressor vector
* `y` – measurement
* `σ` – measurement error bound
* `l` – gain vector
* `γ` – expansion bounds

## Output
* next parameter zonotope

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.identifyStep (X : Zonotope (Vec ℝ n)) (r : Vec ℝ n) (y σ : ℝ)
    (l γ : Vec ℝ n) : Zonotope (Vec ℝ n) :=
  let q : ℝ := max (r ⬝ᵥ X.c - X.supportRadius r) (y - σ)        -- tight strip F_T, lower end
  let u : ℝ := min (r ⬝ᵥ X.c + X.supportRadius r) (y + σ)        -- tight strip F_T, upper end
  let Xh : Zonotope (Vec ℝ n) :=                                  -- Step 3: X̂(λ)
    X.intersectStrip (Matrix.of fun _ j => r j : Mat ℝ 1 n) (fun _ => (u - q) / 2)
      (fun _ => (u + q) / 2) (Matrix.of fun i _ => l i : Mat ℝ n 1)
  Xh.plus { h := n, c := 0, G := fun i => Pi.single i (γ i) }    -- Step 5: X̂(λ) ⊕ γ Bⁿ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
