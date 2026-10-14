module

public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith

@[expose] public section

/-!
# CORA's `eliminateTrueFalse`, as printed

`@stl/eliminateTrueFalse.m` rewrites `φ U[a,b] true` to `true`. Under `modelCheckTrace`'s reading
`φ U[a,b] true` needs `φ` on every step up to a time `t ≥ a`, at least `[0,a]`, so `false U[0,1]
true` is false. `STL.Tree.eliminateTrueFalseCora_until_counterexample` is that;
`STL.Tree.eliminateTrueFalse` keeps the node. (The rewrite of `true R[a,b] ψ` to `true` is right
under that reading.)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eliminateTrueFalse(obj)` as printed. -/
def STL.Tree.eliminateTrueFalseCora (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.eliminateTrueFalseWith (fun _ _ _ => .tt) φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
