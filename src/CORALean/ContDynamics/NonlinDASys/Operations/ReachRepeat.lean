import CORALean.ContDynamics.NonlinDASys.Definitions.ErrorLoopResult
import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# [1, Alg. 1]'s linearization-error loop

Lines 5-10 of `[1, Alg. 1]`, the `repeat` loop: enlarge the errors by `λ` about their centre
(Eq. 17), run `linReach` at the enlarged errors (lines 6-8: `Ũ`, Eq. 4's `Rᵈ(τ_k)`, Prop. 2's
`R(τ_k)`), compute the errors `L` over the joint set (line 9, Cor. 1), and stop when `L ⊆ L̄` or
`L ⊈ L_max`. Cor. 1 needs the Hessian bounds over `R^z`, so it is an argument: `corollary1`, from
the linearization `taylor`, the joint set and `U`. So is the containment test `sub`. The loop has no
stated iteration count, so `fuel` is an argument and the result an `Option`, `none` once `fuel`
enlargements have not reached an exit. The errors are pairs, the dynamics' and the constraint's;
`L_max` bounds the dynamics' only, and `taylor`'s own `Verror` fields are not read.

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

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] lines 5-10 for the start set `Rk` with linearization `taylor`, from the errors `L`
of the previous pass: the last pass, or `none` after `fuel` passes without an exit. -/
noncomputable def NonlinDASys.reachRepeat (sys : NonlinDASys n p m)
    (taylor : NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (Lmax : Zonotope (Vec ℝ n)) (lam r : ℝ) (η : ℕ) (Rk : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) :
    ℕ → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p) → Option (NonlinDASys.ErrorLoopResult n p)
  | 0, _ => none
  | fuel + 1, L =>
      let enlarge : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) := fun Z =>
        ((Z.plus (Zonotope.ofPoint (-Z.c))).mtimes (lam • (1 : Mat ℝ _ _))).plus
          (Zonotope.ofPoint Z.c)                                 -- ĉ ⊕ λ(L ⊕ (−ĉ)), Eq. (17)
      let Lbar := (enlarge L.1, enlarge L.2)                     -- l. 5
      let R := NonlinDASys.linReach (sys.f taylor.xs taylor.ys taylor.us)
        (sys.g taylor.xs taylor.ys taylor.us) taylor.A taylor.B taylor.C taylor.D taylor.E
        taylor.F_inv taylor.xs taylor.ys taylor.us Rk U Lbar.1 Lbar.2 r η  -- l. 6-8
      let Lnew := corollary1 taylor R.2.2 U                      -- l. 9
      if sub Lnew.1 Lbar.1 && sub Lnew.2 Lbar.2 || !sub Lnew.1 Lmax then   -- l. 10
        some ⟨Lbar, R.2.1, R.2.2, Lnew⟩
      else
        NonlinDASys.reachRepeat sys taylor corollary1 sub Lmax lam r η Rk U fuel Lnew

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
