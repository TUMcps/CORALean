module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

/-!
# A nonlinear reset abstracted by its Taylor expansion

[1, Eq. 14]: a reset `r : ℝⁿ → ℝⁿ` expanded to order `γ` around `c = center(F)`,
`p(x) = Σ_{i=0}^{γ} ((x - c)ᵀ∇)ⁱ r(c) / i!`, here coordinate by coordinate with
`Dⁱr₍ⱼ₎(c)(x - c, …, x - c)`, and the remainder set as printed,
`L = {((x - c)ᵀ∇)^{γ+1} r(ξ) / (γ+1)! | ξ ∈ F, x ∈ F}` — one `ξ` for all coordinates.
[1] claims `∀ x ∈ F : r(x) ∈ p(x) ⊕ L`; `Theorems.ResetTaylorCounterexample` refutes it and
`Theorems.ResetTaylorMem` proves it with a `ξ` per coordinate over a convex set.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p(x)`: the order-`γ` Taylor polynomial of `r` at `c`, each coordinate on its own. -/
noncomputable def resetTaylorPoly (r : Vec ℝ n → Vec ℝ n) (γ : ℕ) (c x : Vec ℝ n) : Vec ℝ n :=
  fun j => ∑ i ∈ Finset.range (γ + 1),
    iteratedFDeriv ℝ i (fun y => r y j) c (fun _ => x - c) / (i.factorial : ℝ)

/-- [1]'s `L`: the order-`γ+1` term of the whole map at one `ξ ∈ F`, for any `x ∈ F`. -/
def resetLagrangeSet (r : Vec ℝ n → Vec ℝ n) (γ : ℕ) (c : Vec ℝ n) (F : Set (Vec ℝ n)) :
    Set (Vec ℝ n) :=
  {y | ∃ ξ ∈ F, ∃ x ∈ F,
    y = ((γ + 1).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ (γ + 1) r ξ (fun _ => x - c)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
