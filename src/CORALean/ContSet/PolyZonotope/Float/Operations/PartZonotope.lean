module

public import CORALean.ContSet.PolyZonotope.Float.Operations.PartPatterns

@[expose] public section

/-!
# `PolyZonotope.partZonotope`, over a floating-point scalar

CORA's `@polyZonotope/partZonotope(pZ, id)` (first output `PZ`): the dependent generators are
grouped by their exponent pattern in the factors `id`, and every group but the zero pattern gets a
new factor standing for the monomial of those factors; an all-even pattern's generators are halved
(`FloatOps.half`, exact in a binary format) and a copy of the halves without the new factor is
added. Nothing rounds; centre, independent generators and error box are copied. The grouping
outputs of CORA are not returned.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `partZonotope(pZ, id)`: the polynomial zonotope `PZ`. -/
def PolyZonotope.partZonotope (pZ : PolyZonotope (Vec 𝕋 n)) (V : Finset (Fin pZ.p)) :
    PolyZonotope (Vec 𝕋 n) :=
  -- `unique`: the distinct exponent patterns in the factors `idv`
  let pats := pZ.partPatterns V
  -- the generator's pattern is zero (group 1) or even (`sum(mod(e_vi,2))==0`)
  let isZero : Fin pZ.h → Prop := fun i => ∀ k ∈ V, pZ.E k i = 0
  let isEven : Fin pZ.h → Prop := fun i => ∀ k ∈ V, pZ.E k i % 2 = 0
  -- the groups that get a shift: even and not the zero pattern
  let shifted : Fin pZ.h → Bool := fun i => decide (isEven i ∧ ¬ isZero i)
  -- the group of generator `i`, and the new factor of that group
  let grp : Fin pZ.h → ℕ := fun i => pats.idxOf fun k => if k ∈ V then pZ.E k i else 0
  { p := pZ.p + pats.length
    h := pZ.h + pZ.h
    q := pZ.q
    c := pZ.c
    G := fun l r => Fin.append (fun i => if shifted i then half (pZ.G i r) else pZ.G i r)
      (fun i => if shifted i then half (pZ.G i r) else zero) l
    E := fun r => Fin.append
      (fun i => Fin.addCases (fun k => if k ∈ V then 0 else pZ.E k i)
        (fun g => if ¬ isZero i ∧ grp i = g.val then 1 else 0) r)
      (fun i => Fin.addCases (fun k => if k ∈ V then 0 else pZ.E k i) (fun _ => 0) r)
    GI := pZ.GI
    I_error := pZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
