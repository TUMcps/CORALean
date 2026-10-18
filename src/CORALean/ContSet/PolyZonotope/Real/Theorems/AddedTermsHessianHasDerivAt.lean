module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AddedTermsPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.JacobianHasDerivAt
public import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTermsHessian

@[expose] public section

/-!
# `addedTermsHessian` is the Hessian of the weighted sum

With `F(a) = ∑ᵢ lᵢ · fᵢ(a)` the weighted sum of the dimensions of `pZ.point`, the point of the
first derivative `jacobian k` of `addedTerms` is the derivative of `F` along factor `k`, and
the point of the second is the derivative of that along factor `j`. So `H(a, l)ⱼₖ` is the
second partial `∂ⱼ∂ₖ F`, which is [CORA's documented output]: the Hessian of
`l(1)·pZ₁ + l(2)·pZ₂ + …` in the differentiated factors, at fixed parameter factors.
Both derivatives are real, one-variable `HasDerivAt`s along the factor's line.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first derivative of `F` along `k` is the point of `jacobian k`, and the derivative of that
along `j` is the Hessian entry. -/
theorem PolyZonotope.addedTermsHessian_hasDerivAt (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) (l : Fin n → ℝ) (j k : Fin pZ.p) : -- --- STMT ---
    HasDerivAt (fun t => ∑ i, l i * pZ.point (Function.update a k t) i)
      ((pZ.addedTerms.jacobian (Fin.castAdd n k)).point (Fin.append a l)) (a k)
    ∧ HasDerivAt (fun t => (pZ.addedTerms.jacobian (Fin.castAdd n k)).point
        (Fin.append (Function.update a j t) l))
      (pZ.addedTermsHessian a l j k) (a j) := by -- --- PROOF ---
  -- the sum's factor vector moved along `m` is `append (update a m t) l`
  have hupd : ∀ (m : Fin pZ.p) (t : ℝ), Function.update (Fin.append a l : Fin (pZ.p + n) → ℝ)
      (Fin.castAdd n m) t = Fin.append (Function.update a m t) l := by
    intro m t
    funext x
    -- a factor of `pZ`, then a weight
    refine Fin.addCases (fun x' => ?_) (fun x' => ?_) x
    · by_cases hx : x' = m
      · subst hx
        rw [Fin.append_left, Function.update_self, Function.update_self]
      · rw [Fin.append_left, Function.update_of_ne, Function.update_of_ne hx, Fin.append_left]
        exact fun h => hx (Fin.castAdd_injective _ _ h)
    · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
      exact fun h => by
        have h' := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
        have := m.isLt
        omega
  -- the point of differentiation, read in the sum's factor vector
  have hk : (Fin.append a l : Fin (pZ.p + n) → ℝ) (Fin.castAdd n k) = a k := Fin.append_left a l k
  have hj : (Fin.append a l : Fin (pZ.p + n) → ℝ) (Fin.castAdd n j) = a j := Fin.append_left a l j
  refine ⟨?_, ?_⟩
  -- the first derivative: `jacobian_hasDerivAt` for the sum, whose point is the weighted sum
  · have h := PolyZonotope.jacobian_hasDerivAt pZ.addedTerms (Fin.castAdd n k) (Fin.append a l)
    have heq : (fun t => ∑ i, l i * pZ.point (Function.update a k t) i)
        = fun t => pZ.addedTerms.point
            (Function.update (Fin.append a l : Fin (pZ.p + n) → ℝ) (Fin.castAdd n k) t) := by
      funext t
      exact (PolyZonotope.addedTerms_point pZ (Function.update a k t) l).symm.trans
        (congrArg pZ.addedTerms.point (hupd k t).symm)
    rw [heq, ← hk]
    exact h
  -- the second: `jacobian_hasDerivAt` for the first derivative
  · have h := PolyZonotope.jacobian_hasDerivAt (pZ.addedTerms.jacobian (Fin.castAdd n k))
      (Fin.castAdd n j) (Fin.append a l)
    have heq : (fun t => (pZ.addedTerms.jacobian (Fin.castAdd n k)).point
          (Fin.append (Function.update a j t) l))
        = fun t => (pZ.addedTerms.jacobian (Fin.castAdd n k)).point
            (Function.update (Fin.append a l : Fin (pZ.p + n) → ℝ) (Fin.castAdd n j) t) := by
      funext t
      exact congrArg (pZ.addedTerms.jacobian (Fin.castAdd n k)).point (hupd j t).symm
    rw [heq, ← hj]
    exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
