module

public import Mathlib.Data.List.Range
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.reduceCrashCora`: techniques that `validateOptions` accepts and `reduce` stops on

`getMembers('reductionTechnique')` lists the techniques `validateOptions` accepts for `linearSys`
(`checkDynParameterOptions.m` l. 309-318). The algorithms call `reduce(S, technique, order)` with
three arguments, so `@zonotope/reduce.m` (l. 98) leaves `filterLength = []` and `option = []`:

* `'methB'`: `priv_reduceMethB.m` reads `filterLength(1)` (l. 42), an index into `[]`;
* `'cluster'`: `priv_reduceCluster.m` tests `clusterMethod == 1, ..., 10` against `[]`, no branch
  runs, and the next line reads the unassigned `Cgen`;
* `'methD'`: no `case 'methD'` in `reduce.m`: the `otherwise` branch throws at every call;
* `'methE'`: `priv_reduceMethE.m` (l. 62) computes `Ztrans = Z\P`, and `zonotope` has no `mldivide`;
* `'redistribute'`: `priv_reduceRedistribute.m` takes `nrOfGens` (l. 36) before it deletes the
  short generators (l. 48-49), then indexes the shortened `G` by `setdiff(1:nrOfGens, ind)`.

Modelled: whether the call stops for a `needed` reduction (more than `d*order` generators) and a
tiny generator being present. Read from the source, not run.

# CORA's `reductionTechnique` accepts five techniques that `reduce` cannot run

`'methD'` stops at the first reduction; likewise `'methB'`, `'cluster'`, `'methE'`, and
`'redistribute'` for a generator set with a zero generator: `G = [1 0 1 0; 0 1 1 0]`, `order = 1`
gives `nrOfGens = 4`, three remain, `setdiff(1:4, 1) = [2 3 4]` indexes a `2 x 3` matrix.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's reduce stops on all five accepted techniques
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The techniques of `getMembers('reductionTechnique')`. -/
inductive Zonotope.ReductionTechnique
  | girard | combastel | pca | methA | methB | methC | methD | methE | methF | redistribute
  | cluster | scott | constOpt
  deriving DecidableEq

/-- `getMembers('reductionTechnique')`: every technique is accepted by `validateOptions`. -/
@[step_of Zonotope.reduceCrashCora_crash]
def Zonotope.step_accepted (_ : ReductionTechnique) : Bool := true


-- The model: CORA's code as printed, kept only to be refuted.
/-- Whether `reduce(Z, t, order)` stops with a MATLAB error, for a reduction that is `needed` and
a set with a `tiny` generator, for the five techniques above; `false` stands for "not claimed". -/
def Zonotope.reduceCrashCora (t : ReductionTechnique) (needed tiny : Bool) : Bool :=
  match t with
  | .methB => needed                                   -- filterLength(1) of []
  | .cluster => needed                                 -- Cgen never assigned
  | .methD => true                                     -- no case in the switch
  | .methE => true                                     -- Z\P: no mldivide for zonotope
  | .redistribute => needed && tiny                    -- setdiff(1:nrOfGens, ind) beyond the new G
  | _ => false

-- The model: CORA's code as printed, kept only to be refuted.
/-- `redistribute`: the generators that remain are indexed by `setdiff(1:nrOfGens, ind)` into a
`G` that has `nKept` columns; `true` if an index exceeds it. -/
def Zonotope.redistributeIndexCrashCora (nrOfGens nKept : Nat) (ind : List Nat) : Bool :=
  ((List.range' 1 nrOfGens).filter (fun i => i ∉ ind)).any (fun i => decide (nKept < i))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `validateOptions` accepts the five techniques and `reduce` stops on each. -/
theorem Zonotope.reduceCrashCora_crash : -- --- CONCL ---
    (∀ t ∈ [ReductionTechnique.methB, .methD, .methE, .cluster, .redistribute],
        step_accepted t = true) ∧
      reduceCrashCora .methB true false = true ∧ reduceCrashCora .cluster true false = true ∧
      reduceCrashCora .methD false false = true ∧ reduceCrashCora .methE false false = true ∧
      reduceCrashCora .redistribute true true = true := by -- --- PROOF ---
  refine ⟨fun t _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The witness of `redistribute`: four generators, one zero, `ind = 1`. -/
theorem Zonotope.redistributeIndexCrashCora_crash :
    redistributeIndexCrashCora 4 3 (List.replicate 1 1) = true ∧
      redistributeIndexCrashCora 4 4 (List.replicate 1 1) = false :=
  ⟨rfl, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
