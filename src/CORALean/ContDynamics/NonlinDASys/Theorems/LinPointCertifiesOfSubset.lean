import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies

/-!
# A certificate survives enlarging the error sets

`LinPoint.Certifies` asks the two error zonotopes to hold every consistent point's linearization
errors over the region, and `0 ∈ Verror`: all monotone in the sets. So a run certified at the
errors `L` that [1, Cor. 1] computes is certified at any enlargement `L̄`, which is how
[1, Alg. 1]'s exit `L ⊆ L̄` passes from the errors it computed to the ones it assumed.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A certificate at the errors `V`, `Va` is one at any zonotopes holding them. -/
theorem NonlinDASys.LinPoint.certifies_of_subset (T : NonlinDASys.LinPoint n p m)
    (sys : NonlinDASys n p m) (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (q : ℕ) (x : ℝ → Vec ℝ n)
    (y : ℝ → Vec ℝ p) (u : ℝ → Vec ℝ m) {V V' : Zonotope (Vec ℝ n)}
    {Va Va' : Zonotope (Vec ℝ p)} (hV : V.construct ⊆ V'.construct)
    (hVa : Va.construct ⊆ Va'.construct)
    (h : ({ T with Verror := V, Verror_y := Va } : NonlinDASys.LinPoint n p m).Certifies
      sys U Δt q x y u) :
    ({ T with Verror := V', Verror_y := Va' } : NonlinDASys.LinPoint n p m).Certifies
      sys U Δt q x y u := by
  obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := h
  exact ⟨F, Rz, hF, hR, fun x' y' u' hz hg => hV (hL x' y' u' hz hg),
    fun x' y' u' hz hg => hVa (hLa x' y' u' hz hg), hus, hV h0, hε⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
