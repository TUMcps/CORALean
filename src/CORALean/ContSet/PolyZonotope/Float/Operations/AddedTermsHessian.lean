module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Operations.AddedTerms
public import CORALean.ContSet.PolyZonotope.Float.Operations.MonoBox

@[expose] public section

/-!
# `PolyZonotope.addedTermsHessian`, over a floating-point scalar

CORA's `@polyZonotope/addedTermsHessian`, entry `(j, k)`: the second derivative of `addedTerms`
along factor `k` and then `j`, evaluated over a box of factor values `(a, l)`. The sum's
generator `idx` has the coefficient `E[j, idx] · E[k, idx] · G idx` (the exponents already lowered
by the first derivative), rounded both ways into an interval; the monomials come from `monoBox`
at the twice-lowered exponents, and `Interval.mtimesIntervalMat` multiplies the two. CORA's
`tol`, `H_str` and the split into `id_diff` and `id_param` are not modelled, as in the real layer.

## Inputs
* `pZ` – polynomial zonotope
* `A` – interval of factor values
* `L` – interval of the Lagrange point
* `j` – first factor index
* `k` – second factor index

## Output
* interval enclosing the second derivative of the added terms
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An interval holding the Hessian entry `H(a, l)ⱼₖ` for every `a ∈ A`, `l ∈ L`. -/
def PolyZonotope.addedTermsHessian (pZ : PolyZonotope (Vec 𝕋 n)) (A : Interval (Vec 𝕋 pZ.p))
    (L : Interval (Vec 𝕋 n)) (j k : Fin pZ.p) : Interval 𝕋 :=
  -- the sum and the two factors differentiated
  let T := pZ.addedTerms
  let kk : Fin T.p := Fin.castAdd n k
  let jj : Fin T.p := Fin.castAdd n j
  -- the exponents with `k` lowered once, then `j`
  let E1 : Fin T.p → Fin T.h → ℕ := fun k' i => if k' = kk then T.E kk i - 1 else T.E k' i
  let E2 : Fin T.p → Fin T.h → ℕ := fun k' i => if k' = jj then E1 jj i - 1 else E1 k' i
  -- the coefficients `E[j,i] E[k,i] Gᵢ`, rounded both ways
  let C : Interval (Mat 𝕋 1 T.h) :=
    ⟨fun _ i => nsmulDown (E1 jj i * T.E kk i) (T.G i 0),
      fun _ i => nsmulUp (E1 jj i * T.E kk i) (T.G i 0)⟩
  let r := Interval.mtimesIntervalMat C (PolyZonotope.monoBox E2 (A.append L))
  ⟨r.inf 0, r.sup 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
