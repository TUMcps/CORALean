module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachLTVCora

@[expose] public section

/-!
# CORA's time-varying `linearSysDT` `reach` applies `B{1}` where `B{2}` acts

`linearSysDT({1,1,1}, {0,1,1}, [], {1,1,1}, {0,0,0}, 1)` (cells: `A{i} = 1`, `B{1} = 0`,
`B{2} = B{3} = 1`, `C{i} = 1`, `D{i} = 0`, `c`, `k`, `E`, `F` empty as the constructor demands for
cells), `R0 = {0}`, `tFinal = 2`, with `U = {1}` (`postProcessing` makes it `U = {0}`,
`uTrans = 1`) or with `U = {0}` and an input trajectory whose first two columns are `1`
(`uTransVec`). CORA's own `simulate` steps `x(i+1) = A{i} x(i) + B{i} u(i)`, so the run under
`u ≡ 1` is `0, 0, 1`. `reach` builds `Uadd` from `B{1}` and, without `uTransVec`, never again;
with it, it rebuilds `Uadd` after pass `i` from `B{i}`, so pass `2` again uses `B{1} = 0`. Either
way `LinearSysDT.reachLTVCora` reaches `{0}` at step `2` (all sets are points, so `reduce` at any
order is the identity), and `x(2) = 1` is missed; `C = 1`, `D = 0` make it the output too.
The hypothesis on `uTransVec` only makes `u ≡ 1` the user's input: `B{1} = 0` gives `{0}` for any.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run `0, 0, 1` of `x(i+1) = A{i} x(i) + B{i}·1` is at `1` at step `2`, outside CORA's set
there, with `uTrans = 1` or any `uTransVec` whose first two columns are `1`, at any order `o`. -/
theorem LinearSysDT.reachLTVCora_counterexample (o : ℕ) (uTransVec : Option (ℕ → Vec ℝ 1))
    (hu : ∀ v, uTransVec = some v → v 1 = (fun _ => 1) ∧ v 2 = fun _ => 1) :
    let A : ℕ → Mat ℝ 1 1 := fun _ => 1
    let B : ℕ → Mat ℝ 1 1 := fun i => if i = 1 then 0 else 1
    let x : ℕ → Vec ℝ 1 := fun i => if i ≤ 1 then 0 else fun _ => 1
    let u : Vec ℝ 1 := fun _ => 1
    (x 0 = 0 ∧ ∀ i < 2, x (i + 1) = A (i + 1) *ᵥ x i + B (i + 1) *ᵥ u) ∧
      x 2 ∉ (LinearSysDT.reachLTVCora A B 0 (Zonotope.ofPoint 0) (Zonotope.ofPoint 0)
        (Zonotope.ofPoint 0) u uTransVec o 2).1.construct := by -- --- PROOF ---
  intro A B x u
  refine ⟨⟨rfl, fun i hi => ?_⟩, ?_⟩
  -- the run: `x(1) = 1·0 + 0·1`, `x(2) = 1·0 + 1·1`
  · rcases i with _ | _ | i
    · funext j
      simp [x, A, B, u]
    · funext j
      simp [x, A, B, u]
    · omega
  -- CORA's set at step `2` is the point `0`
  rintro ⟨β, -, hx⟩
  have h0 := congrFun hx 0
  -- `B{1} = 0` annihilates whichever input `Uadd` carries
  cases uTransVec <;>
    simp [x, A, B, u, LinearSysDT.reachLTVCora, Zonotope.reduceGirard, Zonotope.plus,
      Zonotope.mtimes, Zonotope.ofPoint] at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
