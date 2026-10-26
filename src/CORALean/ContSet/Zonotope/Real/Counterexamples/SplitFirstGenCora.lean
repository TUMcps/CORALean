module

public import CORALean.ContSet.Zonotope.Real.Counterexamples.SplitCora
public import CORALean.ContSet.Zonotope.Real.Operations.SplitFirstGen
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `Zonotope.splitFirstGenCora`: `splitFirstGen` as CORA's code runs

`@zonotope/splitFirstGen.m` (l. 39-42) takes `index` as the argmax of `norm(G(:,j)'*G,1)` over the
generators of the original zonotope and calls `split(Z{i}, index)`, which reads it as a generator
of the bounding box (see `Zonotope.splitCora`). For the generators `(1,0), (0,1), (1,1)` it picks
`3` and the box has two. Read from the source, not run; the empty generator list is not modelled.

# CORA's `splitFirstGen` crashes on `zonotope([0;0],[1 0 1; 0 1 1])`

The scores `‖g_jᵀ G‖₁` are `2, 2, 4`, so `index = 3` (l. 39-42 of `@zonotope/splitFirstGen.m`), and
`split(Z, 3)` reads `G(:,3)` of a bounding box with two generators. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* splitting the first generator errors
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `splitFirstGen` for one zonotope, `index` counted from `1`; `none` is the error. -/
noncomputable def Zonotope.splitFirstGenCora (Z : Zonotope (Vec ℝ n)) :
    Option (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) :=
  let h := fun j => ∑ k, |Z.G j ⬝ᵥ Z.G k|
  match (List.finRange Z.h).argmax h with
  | some j => Z.splitCora (j.val + 1)
  | none => none

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `zonotope([0;0],[1 0 1; 0 1 1])`: the generators `(1,0)`, `(0,1)`, `(1,1)`. -/
def Zonotope.aux_three : Zonotope (Vec ℝ 2) :=
  ⟨3, fun _ => 0, fun j i => if j = 0 then (if i = 0 then 1 else 0)
    else if j = 1 then (if i = 0 then 0 else 1) else 1⟩

/-- `splitFirstGen` passes the argmax index on to `split`. -/
private theorem Zonotope.aux_splitFirstGenCora_of_argmax {n : ℕ} {Z : Zonotope (Vec ℝ n)}
    {j : Fin Z.h} (hZ : (List.finRange Z.h).argmax (fun j => ∑ k, |Z.G j ⬝ᵥ Z.G k|) = some j) :
    Z.splitFirstGenCora = Z.splitCora (j.val + 1) := by
  simp [Zonotope.splitFirstGenCora, hZ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `splitFirstGen` picks the generator `(1,1)` and `split` errors on it. -/
theorem Zonotope.splitFirstGen_cora_crash : -- --- CONCL ---
    Zonotope.aux_three.splitFirstGenCora = none := by -- --- PROOF ---
  -- the box has two generators
  have hlen : Zonotope.aux_three.boxCora.h = 2 := by
    simp [Zonotope.boxCora, Zonotope.boxRadiusCora, Zonotope.aux_three, List.finRange,
      List.filter, Fin.sum_univ_three]
    norm_num
  -- the scores are `4` at generator `2` and `2` elsewhere
  have hv : ∀ j : Fin 3, (∑ k : Fin 3, |Zonotope.aux_three.G j ⬝ᵥ Zonotope.aux_three.G k|) =
      if j = 2 then 4 else 2 := by
    intro j
    fin_cases j <;>
      simp [Zonotope.aux_three, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] <;> norm_num
  -- so the argmax is generator `2`, `index = 3`
  have harg : (List.finRange 3).argmax
      (fun j : Fin 3 => ∑ k : Fin 3, |Zonotope.aux_three.G j ⬝ᵥ Zonotope.aux_three.G k|) =
        some 2 := by
    rw [List.argmax_eq_some_iff]
    refine ⟨by simp, fun a _ => ?_, fun a _ h2 => ?_⟩
    · rw [hv, hv]; by_cases h : a = 2 <;> simp [h]; norm_num
    · rw [hv, hv] at h2
      by_cases h : a = 2
      · subst h; simp
      · simp [h] at h2; norm_num at h2
  rw [Zonotope.aux_splitFirstGenCora_of_argmax (j := ⟨2, by decide⟩) harg]
  simp [Zonotope.splitCora, hlen]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
