module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# CORA's `cartProd_` marks a product with an unbounded factor as bounded

`aux_cartProd_polytope_properties` of `@polytope/cartProd_.m` (l. 167-174) sets the cached
`bounded.val` of `P1 x P2` to `true` when EITHER factor's flag is `true`, and to `false` when both
are `false`; a flag is `some b` when set and `none` when empty, and `isBounded` returns the cached
flag first. `polytope([0 1])` has `bounded.val = true` from the constructor
(`aux_computeHiddenProperties`), and `polytope(-1,0)` (`x ≥ 0`) is unbounded with the flag unset.
Their product `[0,1] × [0,∞)` contains points of every height, yet `cartProd(P1,P2)` stores
`bounded.val = true`, so `isBounded` answers `true`. The flags `emptySet`, `fullDim` are not
modelled. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA flags the product of `[0,1]` and `x ≥ 0` bounded, yet it has points of every height
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The cached `bounded` flag of `P1 x P2` from the flags of `P1` and `P2` (`none` for unset). -/
def HPolytope.cartProdBoundedCora (b₁ b₂ : Option Bool) : Option Bool :=
  -- (~isempty(P1.bounded.val) && P1.bounded.val) || (~isempty(P2.bounded.val) && P2.bounded.val)
  if b₁ = some true ∨ b₂ = some true then some true
  -- (~isempty(P1.bounded.val) && ~P1.bounded.val) && (~isempty(P2.bounded.val) && ~P2.bounded.val)
  else if b₁ = some false ∧ b₂ = some false then some false
  else none

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the flags of `[0,1]` (`true`) and of `x ≥ 0` (unset), CORA's product is flagged bounded,
yet `[0,1] × [0,∞)` has points of every height. -/
theorem HPolytope.cartProd_bounded_cora_counterexample :
    HPolytope.cartProdBoundedCora (some true) none = some true ∧
      ∀ R : ℝ, ∃ x : Vec ℝ 2, x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ x 1 ∧ R < x 1 := by -- --- PROOF ---
  refine ⟨by simp [HPolytope.cartProdBoundedCora], fun R => ?_⟩
  refine ⟨fun i => if i = 0 then 0 else max R 0 + 1, ?_, ?_, ?_⟩
  · simp
  · simp
    positivity
  · simp
    linarith [le_max_left R 0]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
