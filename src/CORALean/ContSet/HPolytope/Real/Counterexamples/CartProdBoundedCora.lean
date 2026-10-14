module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `HPolytope.cartProdBoundedCora`: the boundedness flag of `cartProd_` as CORA's code sets it

`aux_cartProd_polytope_properties` of `@polytope/cartProd_.m` (l. 167-174) infers the cached
`bounded` flag of `P1 x P2` from the flags of the factors:

```
if (~isempty(P1.bounded.val) && P1.bounded.val) ...
        || (~isempty(P2.bounded.val) && P2.bounded.val)
    P_out.bounded.val = true;
elseif (~isempty(P1.bounded.val) && ~P1.bounded.val) ...
        && (~isempty(P2.bounded.val) && ~P2.bounded.val)
    P_out.bounded.val = false;
```

The product is bounded when EITHER factor is. `isBounded` returns the cached `P.bounded.val` first.
A flag is `some b` when set and `none` when empty (unknown); the result `none` leaves the flag
empty. The flags `emptySet`, `fullDim` are handled in the lines above and below and are not
modelled. Read from the source, not run.

# CORA's `cartProd_` marks a product with an unbounded factor as bounded

`polytope([0 1])` (one-dimensional, in vertex representation) has `bounded.val = true` set by the
constructor (`aux_computeHiddenProperties`), and `polytope(-1,0)` (`x ≥ 0`) is unbounded with the
flag unset. Their product is `[0,1] × [0,∞)`, which contains points of every height, and
`cartProd(P1,P2)` stores `bounded.val = true`, so `isBounded` answers `true`. Read from the
source, not run.
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
