module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.Global.Tensor
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `VPolytope.representsaHalfspaceCora`: the `'halfspace'` test on vertices, as CORA's code runs

`@polytope/representsa_.m` sends `type = 'halfspace'` to `aux_isHalfspace` (l. 124), whose
vertex branch (l. 357-368) reads, for a one-dimensional polytope,

```
signOfInfs = sign(V(isinf(V)));
```

but the function never defines `V`: the vertex matrix is `P.V_.val`. MATLAB stops with
`Unrecognized function or variable 'V'`. Only a one-dimensional polytope in vertex
representation gets there (a higher dimension answers `false` first); a polytope that
`isemptyobject` counts empty returns earlier. Read from the source, not run.

# CORA's `polytope/representsa_(P, 'halfspace')` errors on a one-dimensional vertex polytope

The polytope `polytope(0)` (a single vertex, in `ℝ¹`) reaches `aux_isHalfspace`'s vertex branch
and its undefined `V`. The answer is `false`: a halfspace `{x | a x ≤ b}`, `a ≠ 0`, is
unbounded and holds `(b - 1)/a` and `(b - 2)/a`, two points a single vertex cannot. Read from the
source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's halfspace test errors on a polytope that is no halfspace
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(P, 'halfspace')`, `P` a nonempty one-dimensional polytope in
vertex representation; `none` is the MATLAB error. -/
def VPolytope.representsaHalfspaceCora (_P : VPolytope (Vec ℝ 1)) : Option Bool :=
  -- P.isVRep.val and dim(P) == 1: `isinf(V)` reads the undefined variable `V`
  none


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's test errors on `polytope(0)`, which is no halfspace. -/
theorem VPolytope.representsa_halfspace_cora_crash :
    ∃ P : VPolytope (Vec ℝ 1), P.representsaHalfspaceCora = none ∧
      ¬ ∃ (a : Vec ℝ 1) (b : ℝ), a 0 ≠ 0 ∧ P.construct = {x | a 0 * x 0 ≤ b} := by -- --- PROOF ---
  refine ⟨⟨1, fun _ => fun _ => 0⟩, rfl, ?_⟩
  rintro ⟨a, b, ha, h⟩
  have hmem : ∀ t : ℝ, 0 ≤ t → (fun _ => (b - t) / a 0 : Vec ℝ 1) ∈
      (VPolytope.mk 1 fun _ => fun _ => (0 : ℝ)).construct → (b - t) / a 0 = 0 := by
    rintro t - ⟨β, -, -, hx⟩
    have := congrFun hx 0
    simpa using this
  have hin : ∀ t : ℝ, 0 ≤ t → (fun _ => (b - t) / a 0 : Vec ℝ 1) ∈
      (VPolytope.mk 1 fun _ => fun _ => (0 : ℝ)).construct := by
    intro t ht
    rw [h]
    show a 0 * ((b - t) / a 0) ≤ b
    rw [mul_div_cancel₀ _ ha]
    linarith
  have h1 := hmem 1 (by norm_num) (hin 1 (by norm_num))
  have h2 := hmem 2 (by norm_num) (hin 2 (by norm_num))
  rw [div_eq_zero_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> first | exact ha ‹_› | linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
