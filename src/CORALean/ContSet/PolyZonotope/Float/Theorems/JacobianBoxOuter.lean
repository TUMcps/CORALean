module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianBox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MonoBoxOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic

@[expose] public section

/-!
# `jacobianBox` encloses the Jacobian

At every factor vector of the box, the Jacobian matrix of the nominal set's dependent point map
(`Real.PolyZonotope.jacobianMat`, whose column `k` is the point of `jacobian k`) lies in
`jacobianBox`: the exact coefficients `E[k,l] Gₗ` lie between their two roundings, the lowered
monomials in `monoBox`, and their products summed in `Interval.mtimesIntervalMat`.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `a` – factor values

## Hypotheses
* `ha` – factor values lie in the box

## Conclusion
* the exact Jacobian lies in the Jacobian box
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.jacobianBox_outer (pZ : PolyZonotope (Vec 𝕋 n)) (X : Interval (Vec 𝕋 pZ.p))
    {a : Vec ℝ pZ.p} (ha : a ∈ X.construct) :
    Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ) a ∈
      (PolyZonotope.jacobianBox pZ X).construct := by -- --- PROOF ---
  rw [PolyZonotope.jacobianBox, Interval.materialiseMat_eq]
  refine Interval.mem_mat_iff.mpr fun i k => ?_
  -- the lowered monomials, and the exact coefficients between their roundings
  have hm := PolyZonotope.monoBox_outer
    (fun k' l => if k' = k then pZ.E k l - 1 else pZ.E k' l) X ha
  have hC : (fun i l => (pZ.E k l : ℝ) * toReal (pZ.G l i)) ∈
      (⟨fun i l => nsmulDown (pZ.E k l) (pZ.G l i), fun i l => nsmulUp (pZ.E k l) (pZ.G l i)⟩ :
        Interval (Mat 𝕋 n pZ.h)).construct :=
    Interval.mem_mat_iff.mpr fun i l => ⟨nsmulDown_le _ _, le_nsmulUp _ _⟩
  have h := Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hC ⟨_, hm, rfl⟩) i
  -- the column's point is that product, coordinate `i`
  have e : Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ) a i k
      = Matrix.mulVec (fun i l => (pZ.E k l : ℝ) * toReal (pZ.G l i))
        (fun l => Real.PolyZonotope.monomial
          (fun k' l => if k' = k then pZ.E k l - 1 else pZ.E k' l) a l) i := by
    simp [Real.PolyZonotope.jacobianMat, Real.PolyZonotope.jacobian, Real.PolyZonotope.point,
      Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rfl
  rw [e]
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
