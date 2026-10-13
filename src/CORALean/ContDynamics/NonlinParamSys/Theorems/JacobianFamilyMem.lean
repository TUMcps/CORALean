import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
import CORALean.ContSet.Interval.Real.Theorems.ExistsCoeffOfMem
import CORALean.Global.JacobianMatParam

/-!
# The matrix zonotope of the Jacobians holds the Jacobian at every parameter of the box

The Jacobian of a map affine in `p` in the variable `z` is affine in `p` as well: centre
`J f_0 + ∑ cᵢ J fᵢ`, generators `rᵢ J fᵢ`, with `J fᵢ = J f(·, eᵢ) - J f(·, 0)` as CORA's
`aux_parametric` forms it. So for every `p` of the box the Jacobian lies in the matrix zonotope
`linearize` builds. `z` is the state or the input: `zA` and `zB` are the two cases.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {k n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.jacobianFamily_mem (F : Vec ℝ k → Vec ℝ q → Vec ℝ n)
    (hAff : ∀ z p, F z p = F z 0 + ∑ i, p i • (F z (Pi.single i 1) - F z 0)) (z : Vec ℝ k)
    (hd : ∀ p, DifferentiableAt ℝ (fun w => F w p) z) (I : Interval (Vec ℝ q)) {p : Vec ℝ q}
    (hp : p ∈ I.construct) :
    jacobianMat (fun w => F w p) z ∈
      (⟨q, jacobianMat (fun w => F w 0) z + ∑ i, I.center i •
          (jacobianMat (fun w => F w (Pi.single i 1)) z - jacobianMat (fun w => F w 0) z),
        fun i => I.radius i • (jacobianMat (fun w => F w (Pi.single i 1)) z
          - jacobianMat (fun w => F w 0) z)⟩ :
        Zonotope (Mat ℝ n k)).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, hpi⟩ := I.exists_coeff_of_mem hp
  refine ⟨β, hβ, ?_⟩
  -- the map is `F(·, 0) + ∑ pᵢ (F(·, eᵢ) - F(·, 0))`, so its Jacobian is that of the pieces
  have hmap : (fun w => F w p)
      = fun w => F w 0 + ∑ i, p i • (F w (Pi.single i 1) - F w 0) := funext fun w => hAff w p
  have hdi : ∀ i, DifferentiableAt ℝ (fun w => F w (Pi.single i 1) - F w 0) z :=
    fun i => (hd _).sub (hd 0)
  rw [hmap, jacobianMat_param _ _ p z (hd 0) hdi]
  simp only [jacobianMat_sub _ _ z (hd _) (hd 0)]
  -- split each parameter into the centre's part and the generator's
  have hsum : ∀ i, p i • (jacobianMat (fun w => F w (Pi.single i 1)) z
        - jacobianMat (fun w => F w 0) z)
      = I.center i • (jacobianMat (fun w => F w (Pi.single i 1)) z
        - jacobianMat (fun w => F w 0) z)
        + β i • (I.radius i • (jacobianMat (fun w => F w (Pi.single i 1)) z
        - jacobianMat (fun w => F w 0) z)) := fun i => by
    rw [hpi i, add_smul, mul_smul]
  simp only [Finset.sum_congr rfl fun i _ => hsum i, Finset.sum_add_distrib]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
