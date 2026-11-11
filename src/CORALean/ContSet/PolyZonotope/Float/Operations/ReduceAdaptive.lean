module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GirardMetric
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.reduceAdaptive`

CORA's `reduce(pZ, 'adaptive', diagpercent)` (`priv_reduceAdaptive`): the dependent generators
ranked by `‖g‖₁` (halved when every exponent is even), the independent ones by `‖g‖₁ - ‖g‖∞`,
smallest first in one stable ranking. Along it the box distance grows by `½‖Σ|g|‖₂` over the
dependent and by `2‖Σ(|g| with its largest entry zeroed)‖₂` over the independent generators; the
longest prefix within `dHmax = ½ · diagpercent · ‖Σ|g|‖₂` is boxed by `reduceBy`, sound at every
partition. CORA halves the box of an even-exponent generator and moves its center; here the box is
the full radius, sound and a little wider.

## Inputs
* `pZ` – polynomial zonotope
* `diagpercent` – admissible distance, relative to the box diagonal
* `p` – square root precision

## Output
* polynomial zonotope with the selected generators boxed
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `halfs`: the dependent generators whose exponents are all even. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveHalfs (pZ : PolyZonotope (Vec 𝕋 n)) (j : Fin pZ.h) : Bool :=
  (List.finRange pZ.p).all fun k => pZ.E k j % 2 == 0

/-- `m_dep` and `m_indep` as one family, dependent generators first. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveMetric (pZ : PolyZonotope (Vec 𝕋 n)) : Fin (pZ.h + pZ.q) → 𝕋 :=
  Fin.append
    (fun j => sumUp fun i =>
      absolute (if pZ.step_adaptiveHalfs j then half (pZ.G j i) else pZ.G j i))
    (PolyZonotope.girardMetric pZ.GI)

/-- The ranking of `mink([m_dep, m_indep])`: the index at each rank, ties in index order. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveRank (pZ : PolyZonotope (Vec 𝕋 n)) :
    Equiv.Perm (Fin (pZ.h + pZ.q)) :=
  sortPerm fun a b => le (pZ.step_adaptiveMetric a) (pZ.step_adaptiveMetric b)

/-- `hext` for the dependent generators (`hadapG`): the increments of `½‖cumsum(|g|)‖₂` in their
own ranking, one entry per generator. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveIncDep (pZ : PolyZonotope (Vec 𝕋 n)) (p : ℕ) : Array 𝕋 :=
  let m := fun a : Fin pZ.h => pZ.step_adaptiveMetric (Fin.castAdd pZ.q a)
  let rk := sortPerm fun a b => le (m a) (m b)
  ((List.finRange pZ.h).map rk).foldl
    (fun (s : Array 𝕋 × 𝕋 × Array 𝕋) a =>
      let acc := Array.ofFn fun i : Fin n => addUp (s.1.getD i.val zero) (absolute (pZ.G a i))
      let dist := half (normUp p (fun i : Fin n => acc.getD i.val zero))  -- 0.5*vecnorm(cumsum)
      (acc, dist, s.2.2.set! a.val (subUp dist s.2.1)))
    (Array.replicate n zero, zero, Array.replicate pZ.h zero) |>.2.2

/-- `hext` for the independent generators (`hadapGI`): the increments of
`2‖cumsum(|g| - μ)‖₂` in their own ranking, one entry per generator. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveIncIndep (pZ : PolyZonotope (Vec 𝕋 n)) (p : ℕ) : Array 𝕋 :=
  let m := PolyZonotope.girardMetric pZ.GI
  let rk := sortPerm fun a b => le (m a) (m b)
  let off := fun (a : Fin pZ.q) (i : Fin n) =>                       -- |GI| - μ
    if (List.finRange n).find? (fun k => le (maximumOver fun r => absolute (pZ.GI a r))
        (absolute (pZ.GI a k))) = some i then zero else absolute (pZ.GI a i)
  ((List.finRange pZ.q).map rk).foldl
    (fun (s : Array 𝕋 × 𝕋 × Array 𝕋) a =>
      let acc := Array.ofFn fun i : Fin n => addUp (s.1.getD i.val zero) (off a i)
      let dist := mulUp (addUp one one)                                -- 2*vecnorm(GIdiag)
        (normUp p (fun i : Fin n => acc.getD i.val zero))
      (acc, dist, s.2.2.set! a.val (subUp dist s.2.1)))
    (Array.replicate n zero, zero, Array.replicate pZ.q zero) |>.2.2

/-- How many generators CORA's rule boxes, counted in rank order: the longest prefix whose
cumulative distance `cumsum(hext)` is at most `dHmax`. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveCount (pZ : PolyZonotope (Vec 𝕋 n))
    (rank : Equiv.Perm (Fin (pZ.h + pZ.q))) (incD incI : Array 𝕋) (diagpercent : 𝕋) (p : ℕ) :
    ℕ :=
  let Gbox : Vec 𝕋 n := fun i => addUp                                -- Gbox = sum([Gabs,GIabs],2)
    (sumUp fun j => absolute (if pZ.step_adaptiveHalfs j then half (pZ.G j i) else pZ.G j i))
    (sumUp fun j => absolute (pZ.GI j i))
  let dHmax := mulUp (mulUp diagpercent (half one)) (normUp p Gbox)  -- (diagpercent*0.5)*norm
  let inc := fun a : Fin (pZ.h + pZ.q) =>
    Fin.addCases (motive := fun _ => 𝕋) (fun j => incD.getD j.val zero)
      (fun j => incI.getD j.val zero) a
  let cum := ((List.finRange (pZ.h + pZ.q)).map rank).foldl
    (fun (s : 𝕋 × ℕ × ℕ) a =>
      let acc := addUp s.1 (inc a)
      let k := s.2.1 + 1
      (acc, k, if le acc dHmax then k else s.2.2)) (zero, 0, 0)
  cum.2.2                                                             -- redUntil

/-- The ranks below `r` are boxed: the generator is selected. -/
@[step_of PolyZonotope.reduceAdaptive]
def PolyZonotope.step_adaptiveRed (pZ : PolyZonotope (Vec 𝕋 n))
    (rank : Equiv.Perm (Fin (pZ.h + pZ.q))) (r : ℕ) (a : Fin (pZ.h + pZ.q)) : Bool :=
  Nat.blt (rank.symm a).val r


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(pZ, 'adaptive', diagpercent)`: the generators the rule selects boxed into the
independent block, the others kept in their order. -/
def PolyZonotope.reduceAdaptive (pZ : PolyZonotope (Vec 𝕋 n)) (diagpercent : 𝕋) (p : ℕ) :
    PolyZonotope (Vec 𝕋 n) :=
  let rank := pZ.step_adaptiveRank                                  -- idx, ascending
  let r := pZ.step_adaptiveCount rank (pZ.step_adaptiveIncDep p) (pZ.step_adaptiveIncIndep p)
    diagpercent p
  (pZ.reduceBy
    (Partition.ofPred fun j : Fin pZ.h => pZ.step_adaptiveRed rank r (Fin.castAdd pZ.q j) = true)
    (Partition.ofPred fun j : Fin pZ.q =>
      pZ.step_adaptiveRed rank r (Fin.natAdd pZ.h j) = true)).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
