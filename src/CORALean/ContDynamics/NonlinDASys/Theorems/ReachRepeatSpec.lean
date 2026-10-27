module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachRepeat

@[expose] public section

/-!
# What the error loop of [1, Alg. 1] returns

A last pass of lines 5-10 is one whose time-interval set is `linReach` at the assumed errors it
carries (lines 6-8) and whose exit test holds: `L ⊆ L̄` for both errors, or `L ⊈ L_max`
(line 10). By induction on the passes, each either the exit or the pass before it.

## Inputs
* `sys` – system
* `taylor` – linearization of the start set
* `corollary1` – error-set computation
* `sub` – subset test
* `Lmax` – bound on the linearization errors
* `lam` – enlargement factor
* `r` – step size
* `η` – Taylor order
* `Rk` – start set
* `U` – input zonotope
* `fuel` – iteration bound
* `L` – previous errors

## Hypotheses
* none

## Conclusion
* the loop's result is `linReach` at its assumed errors and its exit test holds

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] lines 6-10: the loop's result is `linReach` at its assumed errors, and its exit
test holds. -/
theorem NonlinDASys.reachRepeat_spec (sys : NonlinDASys n p m) (taylor : NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool) (Lmax : Zonotope (Vec ℝ n))
    (lam r : ℝ) (η : ℕ) (Rk : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (fuel : ℕ)
    (L : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)) : -- --- CONCL ---
    ∀ rr ∈ NonlinDASys.reachRepeat sys taylor corollary1 sub Lmax lam r η Rk U fuel L,
      rr.Rti = (NonlinDASys.linReach (sys.f taylor.xs taylor.ys taylor.us)
          (sys.g taylor.xs taylor.ys taylor.us) taylor.A taylor.B taylor.C taylor.D taylor.E
          taylor.F_inv taylor.xs taylor.ys taylor.us Rk U rr.Lbar.1 rr.Lbar.2 r η).2.1 ∧
        (sub rr.L.1 rr.Lbar.1 && sub rr.L.2 rr.Lbar.2
          || !sub rr.L.1 Lmax) = true := by -- --- PROOF ---
  intro rr (h : NonlinDASys.reachRepeat sys taylor corollary1 sub Lmax lam r η Rk U fuel L = some
      rr)
  induction fuel generalizing L with
  | zero => simp [NonlinDASys.reachRepeat] at h
  | succ fuel ih =>
    simp only [NonlinDASys.reachRepeat] at h
    split at h
    · next hc =>
      obtain rfl := Option.some.inj h
      exact ⟨rfl, hc⟩
    · exact ih _ h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
