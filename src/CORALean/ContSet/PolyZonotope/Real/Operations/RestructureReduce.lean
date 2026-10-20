module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure

@[expose] public section

/-!
# `PolyZonotope.restructureReduce`

CORA's `restructure` at its `reduce` methods: the same conversion, with a reduction ahead of
it. `restructure` alone fixes the *factor* count at `n` but carries every dependent generator
across; reducing first bounds the generator count too, which is why CORA parameterises by an
order. Reduce first and restructure after: `reduce` returns a diagonal independent block, so
restructuring last leaves it empty. CORA's four `reduce` variants differ in which generators
they keep; the ranking here is Girard's, from `reduce`.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Output
* reduced polynomial zonotope after restructuring
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reduced to order `o` first, then restructured: no independent generator
left, and a generator count the order bounds. -/
noncomputable def PolyZonotope.restructureReduce (pZ : PolyZonotope (Vec ℝ n))
    (o : ℕ) : PolyZonotope (Vec ℝ n) :=
  (pZ.reduce o).restructure

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
