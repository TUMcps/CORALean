module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceSplit
public import CORALean.Global.Sort

@[expose] public section

/-!
# CORA's `reduce(pZ, 'girard', order)` on a polynomial zonotope

`PolyZonotope.reduceSplit` at the generators CORA removes: past `order · n` generators in the two
blocks together, the `order · n - n` longest stay, an even dependent generator counting half its
length, the squared length summed from the last coordinate down; ties keep the earlier generator.
The rest goes through `reduceSplit`. At that count or below only the unused factors go. The
indices of the dependent generators kept come with the set, for the identifiers.
`reduceCora_outer` shows the reduction encloses.

## Inputs
* `pZ` – polynomial zonotope
* `o` – the order
* `order` – the order of the merged exponent columns of the removed part

## Output
* the reduced set and the indices of the dependent generators kept
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(pZ, 'girard', o)`, with the indices of the dependent generators kept. -/
def PolyZonotope.reduceCora (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ)
    (order : ℕ → Array (Array ℕ) → Array ℕ) : PolyZonotope (Vec 𝕋 n) × List ℕ :=
  if o * n < pZ.h + pZ.q then
    -- the squared length of generator `r` of `[G, GI]` (CORA ranks longest first, keeps `order`)
    let len : Fin (pZ.h + pZ.q) → 𝕋 := fun r =>
      let x : Fin n → 𝕋 := fun i =>
        Fin.addCases (motive := fun _ => 𝕋)
          (fun l => if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i)
          (fun j => pZ.GI j i) r
      sumDown fun i : Fin n => mulDown (x (Fin.rev i)) (x (Fin.rev i))
    let perm := sortPerm fun a b : Fin (pZ.h + pZ.q) => le (len b) (len a)
    let K := (o - 1) * n
    let removed : List (Fin (pZ.h + pZ.q)) :=
      ((List.finRange (pZ.h + pZ.q)).filter (fun t => K ≤ t.val)).map perm
    let rD := (removed.filter (fun r => r.val < pZ.h)).map Fin.val
    let rI := (removed.filter (fun r => pZ.h ≤ r.val)).map (fun r => r.val - pZ.h)
    let kD := (List.range pZ.h).filter (fun l => !rD.contains l)
    (pZ.reduceSplit kD.toArray rD.toArray
      ((List.range pZ.q).filter (fun j => !rI.contains j)).toArray rI.toArray order, kD)
  else (pZ.compactFactors, List.range pZ.h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
