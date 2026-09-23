import CORALean.ContSet.Zonotope.Real.Operations.RatioExceeds

/-!
# `Alg. 1` lines 6-10: growing the selection by the ratio test

[1, Alg. 1] lines 6-10: one more generator while the ratio is still over `µ̄`,
carrying line 2's `r_sel` grown by line 8. The fuel is line 6's own bound
`ξ < n_m`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-10: one more generator while the ratio is still over `µ̄`, carrying
line 2's `r_sel` grown by line 8. The fuel is line 6's own bound `ξ < n_m`. -/
def Zonotope.enclRatioLoop (lt : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (rs : Vec ℝ n) (μbar : ℝ) : ℕ → ℕ → Vec ℝ n → ℕ
  | 0, ξ, _ => ξ
  | k + 1, ξ, rsel =>
    if h : ξ < Z.h ∧ Zonotope.ratioExceeds lt rs rsel μbar then
      Z.enclRatioLoop lt σ rs μbar k (ξ + 1)
        (fun j => rsel j + |Z.G (σ ⟨ξ, h.1⟩) j|)
    else ξ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
