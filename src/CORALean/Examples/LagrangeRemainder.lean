import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfHessian
import CORALean.ContSet.Interval.Real.Instances

/-!
# A certificate computed from a field, end to end

`IsAbstractionError` is a certificate someone can produce, and not only assume: `f(x, u) = x₀² + u₀`
over the unit box, expanded at the origin, is certified by `abstrErrLin` with nothing left over.
`γ` is `(1, 1)`, the box's own radius; the second derivative is the constant `2` in the state entry
and `0` elsewhere, so the bound is `½ · 1 · 2 · 1 = 1`, and the true error `x₀²` reaches exactly
`1` at `x₀ = 1`: the certificate is tight, not the vacuous one a mis-stated proposition would
admit. Everything the theorem needs is supplied by hand, as CORA's `hessian` handle supplies it;
`sqProj` is an `abbrev` so that `simp` still reads a coordinate through it.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the square field has the linear abstraction error certificate
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Set ContSet

-- The field: nonlinear in the state, affine in the input.
def Example.sqField : Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1 := fun x u _ => x 0 * x 0 + u 0

-- The same field on the stacked variable `z = [x; u]`, which is where it is expanded.
def Example.sqStacked : Vec ℝ 2 → Vec ℝ 1 := fun z _ => z 0 * z 0 + z 1

-- Reading one coordinate of that variable, which the derivatives are built from.
abbrev Example.sqProj (i : Fin 2) : Vec ℝ 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i

-- The derivative at `ξ`, and the second derivative, which is constant.
noncomputable def Example.sqDeriv (_ : Fin 1) (ξ : Vec ℝ 2) : Vec ℝ 2 →L[ℝ] ℝ :=
  (2 * ξ 0) • Example.sqProj 0 + Example.sqProj 1

noncomputable def Example.sqHess (_ : Fin 1) (_ : Vec ℝ 2) : Vec ℝ 2 →L[ℝ] Vec ℝ 2 →L[ℝ] ℝ :=
  ((2:ℝ) • Example.sqProj 0).smulRight (Example.sqProj 0)

-- The entrywise bound on it, and the unit box the step runs on.
def Example.sqHessBound (_ : Fin 1) : Mat ℝ 2 2 :=
  fun j k => if j = 0 then (if k = 0 then (2:ℝ) else 0) else 0

def Example.sqBox : Zonotope (Vec ℝ 2) := ⟨2, 0, fun k => Pi.single k 1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unit box's abstraction error for `f(x, u) = x₀² + u₀` at the origin,
where `A = 0` and `B = 1` really are the derivative. -/
theorem Example.sq_abstractionError : -- --- CONCL ---
    IsAbstractionError (S := ℐ𝒱) Example.sqField 0 1 0 0
      {x : Vec ℝ 1 | |x 0| ≤ 1} {u : Vec ℝ 1 | |u 0| ≤ 1}
      (abstrErrLin Example.sqHessBound Example.sqBox
        (Fin.append (0 : Vec ℝ 1) (0 : Vec ℝ 1))) := by -- --- PROOF ---
  refine IsAbstractionError.of_hessian (F := Example.sqStacked) (C := univ)
    (Ff := Example.sqDeriv) (Hf := Example.sqHess) ?_ convex_univ (mem_univ _)
    (subset_univ _) ?_ ?_ ?_ ?_ ?_
  -- the stacked field is the field
  · intro x u; funext i; rfl
  -- the box holds every admissible pair, read off as its own coefficients
  · intro x hx u hu
    refine ⟨fun k => Fin.append x u k, fun k => ?_, ?_⟩
    · fin_cases k
      · exact hx
      · exact hu
    · show (Fin.append x u : Vec ℝ 2) = 0 + ∑ k, (Fin.append x u : Vec ℝ 2) k • Pi.single k 1
      rw [zero_add]
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
  -- the first derivative, by the product rule on the two coordinates
  · intro i ξ _
    have h0 : HasFDerivAt (fun z : Vec ℝ 2 => z 0) (Example.sqProj 0) ξ :=
      (Example.sqProj 0).hasFDerivAt
    have h1 : HasFDerivAt (fun z : Vec ℝ 2 => z 1) (Example.sqProj 1) ξ :=
      (Example.sqProj 1).hasFDerivAt
    have heq : Example.sqDeriv i ξ = ξ 0 • Example.sqProj 0
        + ξ 0 • Example.sqProj 0 + Example.sqProj 1 := by
      ext v; simp [Example.sqDeriv]; ring
    rw [heq]
    exact (h0.mul h0).add h1
  -- the second, the first being linear in `ξ` with a constant tail
  · intro i ξ _
    have h0 : HasFDerivAt (fun z : Vec ℝ 2 => 2 * z 0) ((2:ℝ) • Example.sqProj 0) ξ := by
      simpa using ((Example.sqProj 0).hasFDerivAt).const_mul (2:ℝ)
    exact (h0.smul_const (Example.sqProj 0)).add_const (Example.sqProj 1)
  -- its four entries against the bound
  · intro i ξ _ j k
    fin_cases j <;> fin_cases k <;> simp [Example.sqHess, Example.sqHessBound]
  -- and `A = 0`, `B = 1` as the two blocks of that derivative
  · intro i v w
    fin_cases i
    show (2 * Fin.append (0 : Vec ℝ 1) (0 : Vec ℝ 1) 0) * Fin.append v w 0
      + Fin.append v w 1 = _
    rw [show Fin.append (0 : Vec ℝ 1) (0 : Vec ℝ 1) 0 = 0 from rfl,
      show (Fin.append v w : Vec ℝ 2) 1 = w 0 from rfl]
    simp [Matrix.one_mulVec]

/-- The box that certificate is: `[-1, 1]`, which `x₀ = 1` attains. -/
example : (abstrErrLin Example.sqHessBound Example.sqBox
    (Fin.append (0 : Vec ℝ 1) (0 : Vec ℝ 1))).sup 0 = 1 := by
  have hz : Fin.append (0 : Vec ℝ 1) (0 : Vec ℝ 1) = (0 : Vec ℝ 2) := by
    funext j; fin_cases j <;> rfl
  rw [hz]
  simp [abstrErrLin, Example.sqBox, Example.sqHessBound, dotProduct, mulVec,
    Pi.single_apply, apply_ite (abs : ℝ → ℝ), Finset.filter_eq]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
