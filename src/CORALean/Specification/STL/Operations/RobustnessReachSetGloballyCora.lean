module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# `robustnessReachSetGloballyCora`, CORA's robustness of `G_[0,T] x > 0` on a reach set

CORA's `stl/robustness` (`specification/@stl/robustness.m`) for a `reachSet`, on the path this
model fixes: one branch (`size(R,1) = 1`), numeric time points (`hybrid = false`), one state,
and `globally(x(1) > 0, interval(0,T))`. Its predicate gives `sets{1} = {polytope(1,-eps)}`, the
unsafe `x ≤ -eps` (`aux_reverseInequalityConstraints`, `polytope/not`). A set is the interval
`[lo, hi]` (`zonotope(S)` is not a halfspace); `aux_robustnessSet` (l. 389-468) returns the
quadratic program's `sqrt` of the squared distance when an intersection test fails, else the
linear program's `-r` (the deepest ball in `x ≤ b`), both at their optima, written in closed form.
`aux_robustnessReachSet` (l. 252-305), one `let` per step: `timeStepSize`, `tStart`, `tFinal`,
the non-uniform `linspace` (l. 266-268; `none` on the uniform branch, which the model leaves),
`consistentTimeStep` (globally arm), and per window `aux_findReachSets` (time points first, then
time intervals, each kept when `meets` its time) and the loop of l. 292-297, which overwrites
`r(j,i)` and breaks on `0`. `aux_robustnessTemporalLogic` at depth `0` (l. 136-150) takes the
minimum over the windows `index`; `none` is its `-inf`. `meets` stands for `isIntersecting_(·,·,
'exact',1e-8)` on times, `isectApprox`, `isectExact` for the two set tests of l. 403-404.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `robustness(globally(x(1) > 0, interval(0,T)), R)` for a one-branch reach set of a
one-dimensional system: time points `tp` with sets `Xp`, time intervals `ti` with sets `Xi`, every
set an interval `(lo, hi)`. `none` is the uniform branch, left, or the value `-inf`. -/
noncomputable def STL.robustnessReachSetGloballyCora
    (meets : ℝ × ℝ → ℝ × ℝ → Bool) (isectApprox isectExact : ℝ × ℝ → ℝ → Bool) (eps : ℝ)
    (tp : List ℝ) (Xp : List (ℝ × ℝ)) (ti : List (ℝ × ℝ)) (Xi : List (ℝ × ℝ)) (T : ℝ) :
    Option ℝ :=
  let b := -eps                                               -- sets{1} = ~polytope(-1,0)
  let dts := List.zipWith (· - ·) tp.tail tp                  -- dt = diff(timePoint.time)
  let uniform := (List.zipWith (· - ·) dts.tail dts).all
    (fun d => decide (|d| < 1e-10))                           -- all(abs(diff(dt)) < 1e-10)
  let tStart := tp.headD 0                                    -- tStart = R(1).timePoint.time{1}
  let tFinal := min T (tp.getLastD 0)                         -- min(maximumTime(eq),...{end})
  if uniform then none else
  let N := ⌈(tFinal - tStart) / dts.foldl min (dts.headD 0)⌉₊  -- ceil((tFinal-tStart)/min(dt))
  let t : List ℝ := (List.range N).map
    (fun k => tStart + k * (tFinal - tStart) / (N - 1))      -- t = linspace(tStart,tFinal,N)
  let dt := (tFinal - tStart) / (N - 1)                       -- dt = (tFinal-tStart)/(length(t)-1)
  let fromS := 0 / dt                                         -- from = scale*res.from
  let toS := T / dt                                           -- to = scale*res.to
  let I : ℝ × ℝ :=
    if 1e-10 < |(round fromS : ℝ) - fromS| ∨ 1e-10 < |(round toS : ℝ) - toS| then
      (⌊fromS⌋ * dt, ⌈toS⌉ * dt)                             -- stlInterval(floor(from)*dt,...)
    else (round fromS * dt, round toS * dt)                   -- stlInterval(round(from)*dt,...)
  let robSet : ℝ × ℝ → ℝ := fun S =>                          -- aux_robustnessSet(S,set)
    if !(isectApprox S b) || !(isectExact S b) then
      Real.sqrt ((S.1 - b) ^ 2)                               -- val = sqrt(val), quadprog
    else -(b - S.1)                                           -- [~,val] = CORAlinprog(problem)
  let r : List ℝ := (List.range (N - 1)).map fun i =>         -- for i = 1:length(t)-1
    let w := (t.getD i 0, t.getD (i + 1) 0)                   -- interval(t(i),t(i+1))
    let R_ := ((tp.zip Xp).filter (fun p => meets (p.1, p.1) w)).map Prod.snd ++
      ((ti.zip Xi).filter (fun p => meets p.1 w)).map Prod.snd  -- aux_findReachSets(R,...)
    (R_.foldl (fun acc S => if acc.2 then acc else
      (robSet S, decide (robSet S = 0))) ((0 : ℝ), false)).1  -- r(j,i) = ...; if ~r(j,i) break
  let index := (List.range N).filter
    (fun i => decide (I.1 ≤ t.getD i 0 ∧ t.getD i 0 ≤ I.2))   -- find(time >= from & ...)
  let index := index.filter (· < N - 1)                       -- index(index <= length(r))
  match index with                                            -- r(cnt) = min(r_(index))
  | [] => none
  | i :: rest => some ((rest.map (r.getD · 0)).foldl min (r.getD i 0))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
