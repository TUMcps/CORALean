module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `ConZonotope.supportFuncUpperCora`: the `'upper'` support function as CORA's code computes it

`@conZonotope/supportFunc_.m`, `type = 'upper'`, tests `all(all(cZ.A == 0))` (l. 49) and, if it
holds, returns the unconstrained support value.

CORA's `cZ.A`, `cZ.b` are the equality rows `A ξ = b` (here `P.Ae`, `P.be`). An all-zero `A` is read
as "no constraints", whatever `b` is, though `0 ξ = b` with `b ≠ 0` has no solution. The
unconstrained branch returns `supremum(interval(dir'*cZ))`, the support value of the zonotope
`c + G [-1,1]^h`, `dir·c + Σ |dir·Gⱼ|`. The linear program of the constrained branch is the
parameter `lp`. Read from the source, not run.

# CORA's `conZonotope/supportFunc_(cZ, dir, 'upper')` is finite for an empty set

`cZ` with `c = 0`, one generator `1`, `A = (0)`, `b = (1)` in `ℝ¹` has the constraint `0 ξ = 1`,
which no `ξ` satisfies: the set is empty and its support function is `-Inf`. `supportFunc_` tests
`all(all(cZ.A == 0))` (l. 49), takes the set for unconstrained and returns the support value `1` of
the zonotope `[-1,1]`. The public `supportFunc` answers `-Inf` only if `supportFunc_` throws, which
it does not here. A wrong answer, not unsound: the callers read (`conZonotope/interval.m`, which
compacts away zero rows first, and `contains_.m`, l. 690) do not turn this value into a false
verdict. Read from the source, not run.

## Inputs
* `lp` – value of the linear program

## Hypotheses
* none

## Conclusion
* CORA's upper support function of an empty set is finite
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- CORA's `val` for `supportFunc_(cZ, dir, 'upper')`; `lp` is the value of the linear program
of the constrained branch. -/
noncomputable def ConZonotope.supportFuncUpperCora (cZ : ConZonotope (Vec ℝ n))
    (dir : Vec ℝ n →ₗ[ℝ] ℝ) (lp : EReal) : EReal :=
  -- isempty(cZ.A) || all(all(cZ.A == 0))
  if ∀ i ξ, cZ.P.Ae i ξ = 0 then
    -- aux_supportFunc_unconstrained: val = supremum(interval(dir'*cZ))
    (((dir cZ.c + ∑ j, |dir (cZ.G j)| : ℝ)) : EReal)
  else lp

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `c = 0`, one generator `1`, equality row `0 ξ = 1`. -/
def ConZonotope.aux_infeasibleZeroRow : ConZonotope (Vec ℝ 1) where
  h := 1
  c := fun _ => 0
  G := fun _ _ => 1
  P :=
    { m := 0
      A := Fin.elim0
      b := Fin.elim0
      me := 1
      Ae := fun _ => 0
      be := fun _ => 1 }

theorem ConZonotope.aux_infeasibleZeroRow_construct :
    ConZonotope.aux_infeasibleZeroRow.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, ⟨-, hE⟩, -⟩
  have h0 : ((0 : (Vec ℝ 1) →ₗ[ℝ] ℝ)) β = 1 := hE (0 : Fin 1)
  rw [LinearMap.zero_apply] at h0
  exact absurd h0 (by norm_num)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is empty, so its support value along `dir = id` is `⊥ = -Inf`; CORA answers `1`,
whatever `lp` is. -/
theorem ConZonotope.supportFunc_upper_cora_counterexample (lp : EReal) : -- --- CONCL ---
    ConZonotope.aux_infeasibleZeroRow.construct = ∅ ∧
      (⨆ x ∈ ConZonotope.aux_infeasibleZeroRow.construct,
          (((LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ) x : ℝ) : EReal)) = ⊥ ∧
      ConZonotope.aux_infeasibleZeroRow.supportFuncUpperCora (LinearMap.proj 0) lp =
        1 := by -- --- PROOF ---
  have hc := ConZonotope.aux_infeasibleZeroRow_construct
  refine ⟨hc, by rw [hc]; simp, ?_⟩
  have hall : ∀ (i : Fin ConZonotope.aux_infeasibleZeroRow.P.me)
      (ξ : Vec ℝ ConZonotope.aux_infeasibleZeroRow.h),
      ConZonotope.aux_infeasibleZeroRow.P.Ae i ξ = 0 := fun i ξ => rfl
  unfold ConZonotope.supportFuncUpperCora
  rw [if_pos hall]
  simp [ConZonotope.aux_infeasibleZeroRow]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
