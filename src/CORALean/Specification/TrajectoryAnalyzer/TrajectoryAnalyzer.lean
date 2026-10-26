module

public import CORALean.Global.Interfaces
public import CORALean.Specification.AtomicProposition.AtomicProposition

@[expose] public section

/-!
# Boolean signals of atomic propositions over a simulation

CORA's `trajectoryAnalyzer` (`specification/trajectoryAnalyzer.m`): the points of a simulation
result are tested against atomic propositions, and for each proposition a Boolean `finiteSignal`
records where it holds. The `containers.Map` of propositions is a list of pairs in the order of
`keys(aps)`. `Trajectory` is the part of CORA's `trajectory` it reads, its time points in the time
type `T` and its points in the scalar `𝕋` the simulation is stored in (ℝ, or a float scalar for
both): the time points `t`, the points `x l s` of the realization `s` at the time with index `l`
(both numbered from `1`, as in MATLAB), and the locations `loc` of a hybrid automaton, one for each
time (empty if the system is not hybrid).

## References

None: CORA's `trajectoryAnalyzer.m` cites no source, and the CORA manual (v2026) does not mention
the class.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A simulation result: the time points, the states at each, and the location at each. -/
structure TrajectoryAnalyzer.Trajectory (T 𝕋 : Type) (n : ℕ) where
  t : List T
  x : ℕ → ℕ → Vec 𝕋 n
  loc : List ℕ

/-- A trajectory analyzer: named atomic propositions and the trajectory they are tested on. -/
structure TrajectoryAnalyzer (T 𝕋 : Type) (S : ℕ → Type) (n : ℕ) where
  aps : List (String × AtomicProposition S n)
  traj : TrajectoryAnalyzer.Trajectory T 𝕋 n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
