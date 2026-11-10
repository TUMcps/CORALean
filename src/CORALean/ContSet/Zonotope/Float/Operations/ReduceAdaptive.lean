module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.reduceAdaptive`

CORA's `reduce(Z, 'adaptive', diagpercent)` (`priv_reduceAdaptive`, `'girard'`): generators ranked
by `‖g‖₁ - ‖g‖∞`, smallest first (a stable sort, as MATLAB's `mink`); the metric-zero ones are
boxed for free, then as many of the rest, in rank order, as keep `2 ‖Σ (|g| with its largest entry
zeroed)‖₂` at most `dHmax = 2 · diagpercent · ‖Σ |g|‖₂`. `reduceBy` boxes them and keeps the
others in their original order, as CORA's `sort(idx(...))`. The choice only sizes the result:
`reduceBy` is sound at every partition. CORA's all-zero-metric case drops zero box columns; here
they stay.

## Inputs
* `Z` – zonotope
* `diagpercent` – admissible distance, relative to the box diagonal
* `p` – square root precision

## Output
* zonotope with the selected generators boxed
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The ranking of `mink(normsum - norminf)`: the index at each rank, smallest metric first,
ties in index order. -/
@[step_of Zonotope.reduceAdaptive]
def Zonotope.step_reduceAdaptiveRank (Z : Zonotope (Vec 𝕋 n)) : Equiv.Perm (Fin Z.h) :=
  sortPerm fun j₁ j₂ => le (Z.girardMetric j₁) (Z.girardMetric j₂)

/-- How many generators CORA's adaptive rule boxes, counted in rank order: the metric-zero ones,
then the longest prefix of the rest whose distance bound stays under `dHmax`. -/
@[step_of Zonotope.reduceAdaptive]
def Zonotope.step_reduceAdaptiveCount (Z : Zonotope (Vec 𝕋 n)) (diagpercent : 𝕋) (p : ℕ) : ℕ :=
  let Gabs := fun (j : Fin Z.h) (i : Fin n) => absolute (Z.G j i)       -- Gabs = abs(G)
  let Gbox : Vec 𝕋 n := fun i => sumUp fun j => Gabs j i                -- Gbox = sum(Gabs,2)
  let dHmax := mulUp (mulUp diagpercent (addUp one one)) (normUp p Gbox)  -- dHmax
  let ranked := (List.finRange Z.h).map Z.step_reduceAdaptiveRank            -- idx, ascending
  let zeros := (ranked.filter fun j => le (Z.girardMetric j) zero).length  -- hzeroIdx
  let rest := ranked.drop zeros                                         -- gensred
  -- gensred - mugensred: the largest entry of the column zeroed (its first, as `max` picks)
  let off := fun (j : Fin Z.h) (i : Fin n) =>
    if (List.finRange n).find? (fun k => le (maximumOver (Gabs j)) (Gabs j k)) = some i
    then zero else Gabs j i
  -- cumsum over the columns, the bound `2‖·‖₂` at each, and the last index under dHmax
  let cum := rest.foldl (fun (s : Vec 𝕋 n × ℕ × ℕ) j =>
    let acc : Vec 𝕋 n := fun i => addUp (s.1 i) (off j i)
    let k := s.2.1 + 1
    (acc, k, if le (mulUp (addUp one one) (normUp p acc)) dHmax then k else s.2.2))
    (fun _ => zero, 0, 0)
  zeros + cum.2.2                                                       -- redIdx


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'adaptive', diagpercent)`: the generators the rule selects boxed, the others
kept in their order. -/
def Zonotope.reduceAdaptive (Z : Zonotope (Vec 𝕋 n)) (diagpercent : 𝕋) (p : ℕ) :
    Zonotope (Vec 𝕋 n) :=
  let ranked := (List.finRange Z.h).map Z.step_reduceAdaptiveRank            -- idx, ascending
  let r := min (Z.step_reduceAdaptiveCount diagpercent p) Z.h                -- hzero + redIdx
  let red := (ranked.take r).foldl (fun a j => a.set! j.val true)      -- reduced: the first
    (Array.replicate Z.h false)                                         --   r ranks
  let key := fun (j : Fin Z.h) => red.getD j.val false
  -- stable, kept before reduced, each in index order: CORA's sort(idx(...)) and the rest
  let order := sortPerm fun j₁ j₂ => !key j₁ || key j₂
  Z.reduceBy ((Partition.split (Z.h - r) r).reindex                    -- [Gunred, diag(Gred)]
    (order.symm.trans (finCongr (Nat.sub_add_cancel (Nat.min_le_right _ _)).symm)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
