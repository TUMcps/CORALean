module

public import CORALean.ContSet.Interval.Float.Theorems.AppendConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.AddedTermsHessian
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AddedTermsNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MonoBoxOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTermsHessian

@[expose] public section

/-!
# `addedTermsHessian` encloses the Hessian of the weighted sum

At every factor vector `a` in the box `A` and weights `l` in `L`, the exact layer's Hessian entry
`H(a, l)ⱼₖ` of the nominal set (`Real.PolyZonotope.addedTermsHessian`, the second partial of
`∑ᵢ lᵢ pZᵢ` by `addedTermsHessian_hasDerivAt`) lies in the float entry: the exact coefficients lie
between their two roundings, the twice-lowered monomials in `monoBox`, and their products summed in
`Interval.mtimesIntervalMat`.

## Inputs
* `pZ` – polynomial zonotope
* `A` – interval of factor values
* `L` – interval of the Lagrange point
* `a` – factor values
* `l` – Lagrange point
* `j` – first factor index
* `k` – second factor index

## Hypotheses
* `ha` – factor values lie in the interval
* `hl` – Lagrange point lies in the interval

## Conclusion
* the exact Hessian entry lies between the interval endpoints
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.addedTermsHessian_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (A : Interval (Vec 𝕋 pZ.p)) (L : Interval (Vec 𝕋 n)) {a : Vec ℝ pZ.p} {l : Vec ℝ n}
    (ha : a ∈ A.construct) (hl : l ∈ L.construct) (j k : Fin pZ.p) : -- --- CONCL ---
    toReal (pZ.addedTermsHessian A L j k).inf
        ≤ Real.PolyZonotope.addedTermsHessian (PolyZonotope.nominal pZ) a l j k
    ∧ Real.PolyZonotope.addedTermsHessian (PolyZonotope.nominal pZ) a l j k
        ≤ toReal (pZ.addedTermsHessian A L j k).sup := by -- --- PROOF ---
  -- the stored generators read as the exact ones
  have hG := (PolyZonotope.addedTerms_nominal pZ).1
  -- the appended box of factors and weights holds the appended point
  have hx : (Fin.append a l : Vec ℝ (pZ.p + n)) ∈ (A.append L).construct := by
    rw [Interval.append_construct]
    exact ⟨(a, l), ⟨ha, hl⟩, rfl⟩
  -- the sum, its exact counterpart, and the two lowered exponent matrices
  set T := pZ.addedTerms
  set R := Real.PolyZonotope.addedTerms (PolyZonotope.nominal pZ) with hR
  have hE : T.E = R.E := (PolyZonotope.addedTerms_nominal pZ).2.1
  let kk : Fin T.p := Fin.castAdd n k
  let jj : Fin T.p := Fin.castAdd n j
  let E1 : Fin T.p → Fin T.h → ℕ := fun k' i => if k' = kk then T.E kk i - 1 else T.E k' i
  let E2 : Fin T.p → Fin T.h → ℕ := fun k' i => if k' = jj then E1 jj i - 1 else E1 k' i
  -- the monomials, the coefficients between their roundings, and their product
  have hm := PolyZonotope.monoBox_outer E2 (A.append L) hx
  have hC : (fun (_ : Fin 1) i => ((E1 jj i * T.E kk i : ℕ) : ℝ) * toReal (T.G i 0)) ∈
      (⟨fun _ i => nsmulDown (E1 jj i * T.E kk i) (T.G i 0),
        fun _ i => nsmulUp (E1 jj i * T.E kk i) (T.G i 0)⟩ : Interval (Mat 𝕋 1 T.h)).construct :=
    Interval.mem_mat_iff.mpr fun i l => ⟨nsmulDown_le _ _, le_nsmulUp _ _⟩
  have h := Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hC ⟨_, hm, rfl⟩) 0
  -- the exact entry is that product, coordinate `0`
  have e : Real.PolyZonotope.addedTermsHessian (PolyZonotope.nominal pZ) a l j k
      = Matrix.mulVec (fun (_ : Fin 1) i => ((E1 jj i * T.E kk i : ℕ) : ℝ) * toReal (T.G i 0))
        (fun l' => Real.PolyZonotope.monomial E2 (Fin.append a l) l') 0 := by
    simp only [Real.PolyZonotope.addedTermsHessian, Matrix.of_apply, Real.PolyZonotope.point,
      Real.PolyZonotope.jacobian, Matrix.mulVec, dotProduct]
    rw [zero_add]
    refine Finset.sum_congr rfl fun x _ => ?_
    change Real.PolyZonotope.monomial E2 (Fin.append a l) x •
      ((E1 jj x : ℝ) • ((T.E kk x : ℝ) • R.G x)) = _
    rw [← hG x]
    simp only [smul_eq_mul, Nat.cast_mul]
    ring
  rw [e]
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
