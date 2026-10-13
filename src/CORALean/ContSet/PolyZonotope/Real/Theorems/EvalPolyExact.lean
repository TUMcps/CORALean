module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyFactorCount
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyP
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyStep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyReal
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyStepPoint

@[expose] public section

/-!
# `PolyZonotope.evalPoly` is exactly the polynomial, evaluated coordinatewise

`MulPoint`'s idiom carried through the recursion: the claim is about `point`, not
`construct`, so no product of sets appears, only the coordinatewise image of the
admissible factors under `a ↦ evalPolyReal coeffs (point pZ a)`.

`evalPolyReal` is the same recursion over `ℝ` that `evalPoly` runs over the set,
so the induction matches it step for step — `mul_point` turns the multiplied set
into a product of points, and the centre shift matches `evalPolyReal`'s own step.
It is scalar, so coordinate `i` reads the coefficient list at `i`; that the
polynomials differ between coordinates costs the induction nothing.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `evalPoly_exact` below needs it
/-- `evalPolyP`'s point, at the factor vector its own `p`-proof casts back to
`pZ`'s. Proved by induction, `evalPolyStep_point` carrying the Horner step. -/
theorem PolyZonotope.aux_evalPolyP_point (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n))
    (a : Fin pZ.p → ℝ) :
    (pZ.evalPolyP coeffs).1.point (fun k => a (Fin.cast (pZ.evalPolyP coeffs).2 k))
      = fun i =>
        PolyZonotope.evalPolyReal (coeffs.map fun v => v i) (pZ.point a i) := by -- --- PROOF ---
  -- both the empty and the cons case match `evalPolyP`'s own two-case recursion
  induction coeffs with
  | nil =>
    funext i
    simp [PolyZonotope.evalPolyP, PolyZonotope.point, PolyZonotope.evalPolyReal]
  | cons a0 rest ih =>
    -- `R` is the accumulator one level down, `hR` its shared factor count
    set R := (pZ.evalPolyP rest).1 with hRdef
    set hR := (pZ.evalPolyP rest).2 with hRdef2
    funext i
    show (PolyZonotope.evalPolyStep R pZ hR a0).point (fun k => a (Fin.cast hR k)) i
      = PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i) (pZ.point a i)
    have key : (PolyZonotope.evalPolyStep R pZ hR a0).point (fun k => a (Fin.cast hR k)) i
        = a0 i + R.point (fun k => a (Fin.cast hR k)) i
            * pZ.point (fun k => a (Fin.cast hR (Fin.cast hR.symm k))) i :=
      congrFun (PolyZonotope.evalPolyStep_point R pZ hR a0 (fun k => a (Fin.cast hR k))) i
    have hcancel : (fun k : Fin pZ.p => a (Fin.cast hR (Fin.cast hR.symm k))) = a := by
      funext k; simp
    rw [key, hcancel, congrFun ih i, List.map_cons, PolyZonotope.evalPolyReal]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPoly_exact (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n))
    (a : Fin pZ.p → ℝ) :
    (pZ.evalPoly coeffs).point (fun k => a (Fin.cast (pZ.evalPoly_p coeffs) k))
      = fun i => PolyZonotope.evalPolyReal (coeffs.map fun v => v i) (pZ.point a i) :=
  PolyZonotope.aux_evalPolyP_point pZ coeffs a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
