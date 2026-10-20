module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.PartPatterns

@[expose] public section

/-!
# `PolyZonotope.partZonotope`

CORA's `@polyZonotope/partZonotope(pZ, id)` (first output `PZ`): the dependent generators are
grouped by their exponent pattern in the factors `id`, and every group but the zero pattern gets
a new factor `t ∈ [-1, 1]` standing for the monomial of those factors. An odd pattern's monomial
is `t`; an all-even one lies in `[0, 1]` and is `(1 + t) / 2` (generators halved, a copy without
`t` added: `pZevenShift`). Different patterns get independent factors, hence an enclosure.
Identifiers are positional: the new factors are the rows after `p`, one per distinct pattern,
and constant columns are not folded into the center. CORA's other outputs are not returned.

## Inputs
* `pZ` – polynomial zonotope
* `V` – selected factors

## Output
* polynomial zonotope grouped by the exponent patterns
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `partZonotope(pZ, id)`: the polynomial zonotope `PZ`. -/
noncomputable def PolyZonotope.partZonotope (pZ : PolyZonotope α) (V : Finset (Fin pZ.p)) :
    PolyZonotope α :=
  -- `unique`: the distinct exponent patterns in the factors `idv`
  let pats := pZ.partPatterns V
  -- the generator's pattern is zero (group 1, `pZ_cp`) or even (`sum(mod(e_vi,2))==0`)
  let isZero : Fin pZ.h → Prop := fun i => ∀ k ∈ V, pZ.E k i = 0
  let isEven : Fin pZ.h → Prop := fun i => ∀ k ∈ V, pZ.E k i % 2 = 0
  -- the groups that get a shift: even and not the zero pattern
  let shifted : Fin pZ.h → Prop := fun i => isEven i ∧ ¬ isZero i
  -- the group of generator `i`, and the new factor `ido` of that group
  let grp : Fin pZ.h → ℕ := fun i => pats.idxOf (pZ.partPattern V i)
  { p := pZ.p + pats.length
    h := pZ.h + pZ.h
    q := pZ.q
    c := pZ.c
    -- `pZgen = polyZonotope(0, [ci,Gi], ..)` with halved `Gi` of an even group, then `pZevenShift`
    G := Fin.append (fun i => if shifted i then (1 / 2 : ℝ) • pZ.G i else pZ.G i)
      (fun i => if shifted i then (1 / 2 : ℝ) • pZ.G i else 0)
    -- `[zeros(np,1), eMp_i; ones(1,1+size(eMp_i,2))]`: the exponents in `idp`, and 1 at `ido`
    E := fun r => Fin.append
      (fun i => Fin.addCases (fun k => if k ∈ V then 0 else pZ.E k i)
        (fun g => if ¬ isZero i ∧ grp i = g.val then 1 else 0) r)
      (fun i => Fin.addCases (fun k => if k ∈ V then 0 else pZ.E k i) (fun _ => 0) r)
    GI := pZ.GI }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
