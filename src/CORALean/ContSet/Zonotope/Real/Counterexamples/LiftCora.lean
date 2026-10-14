module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `Zonotope.liftCora`: `lift_` as CORA's code runs, for a `proj` of length `N`

`@zonotope/lift_.m` (and the identical `lift_.m` of `conZonotope`, `zonoBundle`, `capsule` and
`ellipsoid`):

```
if length(proj) == N
    % use project
    Z = project(Z,proj);
else
    throw(CORAerror('CORA:notDefined', ...))
```

`contSet/lift.m` documents `proj` as the "states of the high-dimensional space that correspond to
the states of the low-dimensional set": state `i` of the set becomes state `proj(i)`, which is
how `@interval/lift_.m` (`lb(proj) = I.inf`) and `@polytope/lift_.m` (`A(:,dims) = P.A_.val`)
read it. `project(S,dims)` has the inverse meaning, state `i` of the result is state `dims(i)` of
`S`. The two agree only where `proj` is its own inverse. Read from the source, not run.

# CORA's `lift` of a zonotope applies the inverse permutation

`lift(zonotope([1;2;3]),3,[2 3 1])` moves state 1 to position 2, state 2 to position 3 and state 3
to position 1, giving the point `(3;1;2)`; `project(Z,[2 3 1])` is `(2;3;1)`. The same call on
`interval([1;2;3])` gives `(3;1;2)`, so the classes disagree. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `lift_(Z, N, proj)` with `length(proj) == N`: `project(Z, proj)`. -/
def Zonotope.liftCora (Z : Zonotope (Vec ℝ N)) (proj : Fin N → Fin N) : Zonotope (Vec ℝ N) :=
  Z.project proj

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For the point `(1,2,3)` and the permutation `proj = [2 3 1]`, `lift_` returns `(2,3,1)`, not
the lift `(3,1,2)`, in which state `i` of the set is state `proj i` of the result. -/
theorem Zonotope.lift_cora_counterexample :
    ∃ (Z : Zonotope (Vec ℝ 3)) (proj : Fin 3 → Fin 3), Function.Bijective proj ∧
      (Z.liftCora proj).construct ≠
        {x : Vec ℝ 3 | ∃ y ∈ Z.construct, ∀ i, x (proj i) = y i} := by -- --- PROOF ---
  let proj : Fin 3 → Fin 3 := ![1, 2, 0]
  let c : Vec ℝ 3 := fun i => (i.val : ℝ) + 1
  let Z : Zonotope (Vec ℝ 3) := ⟨0, c, Fin.elim0⟩
  refine ⟨Z, proj, by decide, fun h => ?_⟩
  let x : Vec ℝ 3 := ![3, 1, 2]
  have hx : x ∈ {x : Vec ℝ 3 | ∃ y ∈ Z.construct, ∀ i, x (proj i) = y i} := by
    refine ⟨c, ⟨Fin.elim0, fun j => j.elim0, by simp [Z]⟩, fun i => ?_⟩
    fin_cases i <;> simp [x, proj, c]
    all_goals norm_num
  rw [← h] at hx
  obtain ⟨β, -, hβ⟩ := hx
  have h0 := congrFun hβ 0
  simp [Zonotope.liftCora, Zonotope.project, Zonotope.map, Z, c, x, proj] at h0
  norm_num at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
