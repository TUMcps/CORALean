module

public import Mathlib.Data.List.Range

@[expose] public section

/-!
# `MatExp.expmIndMixedPolytopeCora`: `expmIndMixed` of a matrix polytope as CORA's code runs it

`@matPolytope/simplePlus.m` (l. 31-33) reads the size of its first summand from a variable that
does not exist:

```
matV1 = summand1.V;
[n1,m1,h1] = size(Z1);
```

(`matV1` was meant). `@matPolytope/expmIndMixed.m` (l. 38-43), the only caller, runs

```
for i=1:intermediateOrder
    ePpow = ePpow*matP;
    eP = simplePlus(eP, ePpow*(1/factorial(i)));
end
```

so its first iteration stops with `Unrecognized function or variable 'Z1'`. `none` is the error.
Read from the source, not run.

# CORA's `expmIndMixed(matPolytope, k, maxOrder)` crashes for every `k >= 1`

`expmIndMixed(matPolytope(V), 1, 3)` for any vertex array `V` throws in `simplePlus`; only
`intermediateOrder = 0`, which skips the loop, reaches the interval part. `matPolytope.m` declares
`simplePlus` with the comment `% ?`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `simplePlus(eP, ...)`: `size(Z1)` of an undefined variable, the error. -/
def MatExp.simplePlusPolytopeCora : Option Unit := none

/-- CORA's loop of `expmIndMixed` over `i = 1:intermediateOrder`, each pass calling `simplePlus`. -/
def MatExp.expmIndMixedPolytopeCora (intermediateOrder : ℕ) : Option Unit :=
  (List.range intermediateOrder).foldlM (fun _ _ => MatExp.simplePlusPolytopeCora) ()


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `intermediateOrder >= 1` ends in the error of the first `simplePlus`. -/
theorem MatExp.expmIndMixedPolytope_cora_counterexample {k : ℕ} (hk : 1 ≤ k) :
    MatExp.expmIndMixedPolytopeCora k = none := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [MatExp.expmIndMixedPolytopeCora, List.range_succ_eq_map]
  simp [List.foldlM, MatExp.simplePlusPolytopeCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
