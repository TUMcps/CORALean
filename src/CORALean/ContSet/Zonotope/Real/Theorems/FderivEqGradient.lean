import CORALean.ContSet.Zonotope.Real.Definitions.Gradient
import CORALean.ContSet.Zonotope.Real.Theorems.DerivLine
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Mul

/-!
# The derivative of a set function is its gradient set

[1, Def. 3]: where a function `f` of a zonotope `Y = ⟨c, G⟩` is differentiable, in the centre and
the generator entries together, its derivative in the direction `(u, U)` is read off the gradient
set `∇_Y f = ⟨∇_c f, ∇_G f⟩`: `Df(u, U) = ⟨u, ∇_c f⟩ + Σⱼ ⟨Uⱼ, (∇_G f)ⱼ⟩`, the inner products of
the centre direction with the centre gradient and of each generator direction with its own. The
gradient set is the partial derivatives along single entries, and a direction is the sum of the
single-entry ones, `Df` being linear: the step the chain-rule proofs of [1, Prop. 13 (linear)] and
[1, Prop. 14] take as `Σᵢ c'ₖ(i) ∇cₖ(i) + Σᵢ Σⱼ G'ₖ(i,j) ∇Gₖ(i,j)`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.fderiv_eq_gradient (ℒ : Zonotope (Vec ℝ n) → ℝ) (Y : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ n × (Fin Y.h → Vec ℝ n) => ℒ ⟨Y.h, p.1, p.2⟩)
      (Y.c, Y.G))
    (u : Vec ℝ n) (U : Fin Y.h → Vec ℝ n) :
    fderiv ℝ (fun p : Vec ℝ n × (Fin Y.h → Vec ℝ n) => ℒ ⟨Y.h, p.1, p.2⟩) (Y.c, Y.G) (u, U) =
      u ⬝ᵥ (Y.gradient ℒ).c + ∑ l, U l ⬝ᵥ (Y.gradient ℒ).G l := by -- --- PROOF ---
  set F : Vec ℝ n × (Fin Y.h → Vec ℝ n) → ℝ := fun p => ℒ ⟨Y.h, p.1, p.2⟩ with hFdef
  set D := fderiv ℝ F (Y.c, Y.G) with hD
  -- the gradient's entries are `D` at the single-entry directions
  have hc : ∀ i, (Y.gradient ℒ).c i = D (Pi.single i 1, 0) := fun i => by
    show deriv (fun t => ℒ { Y with c := Function.update Y.c i t }) (Y.c i) = _
    rw [← deriv_line F (Y.c, Y.G) (Pi.single i 1, 0) hF (Y.c i)]
    congr 1
    funext t
    -- the point with entry `i` set to `t` lies on the line
    have hpair : (Function.update Y.c i t, Y.G) =
        (Y.c, Y.G) + (t - Y.c i) • ((Pi.single i 1 : Vec ℝ n), (0 : Fin Y.h → Vec ℝ n)) := by
      refine Prod.ext ?_ (by simp)
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    exact congrArg F hpair
  -- and likewise along a generator entry
  have hG : ∀ l i, (Y.gradient ℒ).G l i = D (0, Pi.single l (Pi.single i 1)) := fun l i => by
    show deriv (fun t => ℒ { Y with G := Function.update Y.G l (Function.update (Y.G l) i t) })
      (Y.G l i) = _
    rw [← deriv_line F (Y.c, Y.G) (0, Pi.single l (Pi.single i 1)) hF (Y.G l i)]
    congr 1
    funext t
    have hpair : (Y.c, Function.update Y.G l (Function.update (Y.G l) i t)) =
        (Y.c, Y.G) + (t - Y.G l i) •
          ((0 : Vec ℝ n), (Pi.single l (Pi.single i 1) : Fin Y.h → Vec ℝ n)) := by
      refine Prod.ext (by simp) ?_
      funext l' k
      by_cases hl : l' = l
      · subst hl
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · simp [hl]
    exact congrArg F hpair
  -- a direction is the sum of the single-entry ones
  have hdec : ((u, U) : Vec ℝ n × (Fin Y.h → Vec ℝ n)) =
      ∑ i, u i • ((Pi.single i 1 : Vec ℝ n), (0 : Fin Y.h → Vec ℝ n)) +
        ∑ l, ∑ i, U l i • ((0 : Vec ℝ n), (Pi.single l (Pi.single i 1) : Fin Y.h → Vec ℝ n)) := by
    refine Prod.ext ?_ ?_
    · funext k; simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · funext l k; simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  -- `D` is linear, so it is the sum of the entries' values
  rw [hdec, map_add, map_sum, map_sum]
  simp only [map_smul, map_sum, hc, hG, smul_eq_mul, dotProduct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
