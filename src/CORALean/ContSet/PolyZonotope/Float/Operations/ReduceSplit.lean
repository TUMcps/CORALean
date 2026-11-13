module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
public import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard

@[expose] public section

/-!
# `PolyZonotope.reduceSplit`

CORA's `reduce(pZ, 'girard', order)` once the generators to keep and to remove are chosen: the
removed ones, a polynomial zonotope about the origin, go through the constructor (equal exponent
columns added), `zonotope(pZtemp)` and the Girard reduction to order 1 of that zonotope; its center
joins the center and its generators the independent generators of the kept part, and the factors no
generator reads are dropped. Which generators are removed (the shortest, by CORA's ranking) is
chosen outside; `reduceSplit` encloses for every choice, and returns the set where the four index
lists are not a partition of the generators.

## Inputs
* `pZ` – polynomial zonotope
* `kD` – the dependent generators kept
* `rD` – the dependent generators removed
* `kI` – the independent generators kept
* `rI` – the independent generators removed
* `order` – the order of the merged exponent columns of the removed part (`construct`)

## Output
* polynomial zonotope of the kept generators and the box of the removed ones
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set of the kept generators plus the order-1 box of the removed ones; the set itself where
the lists are not a partition. -/
def PolyZonotope.reduceSplit (pZ : PolyZonotope (Vec 𝕋 n)) (kD rD kI rI : Array ℕ)
    (order : ℕ → Array (Array ℕ) → Array ℕ) : PolyZonotope (Vec 𝕋 n) :=
  if hv : (kD.toList ++ rD.toList).Perm (List.range pZ.h) ∧
      (kI.toList ++ rI.toList).Perm (List.range pZ.q) then
    -- every listed index is below the count
    have hD : ∀ m, m ∈ kD.toList ++ rD.toList → m < pZ.h := fun m hm =>
      List.mem_range.mp (hv.1.mem_iff.mp hm)
    have hI : ∀ m, m ∈ kI.toList ++ rI.toList → m < pZ.q := fun m hm =>
      List.mem_range.mp (hv.2.mem_iff.mp hm)
    -- `pZtemp = polyZonotope(zeros(N,1), Grem, GIrem, Erem)` of the removed generators
    let R : PolyZonotope (Vec 𝕋 n) :=
      { p := pZ.p, h := rD.size, q := rI.size, c := fun _ => zero,
        G := fun t => pZ.G ⟨rD[t.val]'t.isLt, hD _ (by simp)⟩,
        E := fun k t => pZ.E k ⟨rD[t.val]'t.isLt, hD _ (by simp)⟩,
        GI := fun t => pZ.GI ⟨rI[t.val]'t.isLt, hI _ (by simp)⟩, I_error := Interval.origin n }
    -- `zonoRed = reduce(zonotope(pZtemp), 'girard', 1)`
    let Zr := (R.construct order).zonotopeFold.reduceGirard 1
    -- the kept generators, `c + center(zonoRed)` and `[GI, generators(zonoRed)]`
    let K : PolyZonotope (Vec 𝕋 n) :=
      { pZ with
        h := kD.size
        q := kI.size
        G := fun t => pZ.G ⟨kD[t.val]'t.isLt, hD _ (by simp)⟩
        E := fun k t => pZ.E k ⟨kD[t.val]'t.isLt, hD _ (by simp)⟩
        GI := fun t => pZ.GI ⟨kI[t.val]'t.isLt, hI _ (by simp)⟩ }
    (K.plus Zr.ofIndep).compactFactors
  else pZ.compactFactors

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
