import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure

/-!
# `PolyZonotope.restructureReduce`

CORA's `restructure` at its `reduce` methods: the same conversion, with a
reduction ahead of it. `restructure` alone fixes the *factor* count at `n` but
carries every dependent generator it was given across; reducing first is what
bounds the generator count too, which is why CORA parameterises by an order.

Reduce first and restructure after, not the other way round: `reduce` returns a
diagonal independent block, so restructuring last is what leaves the independent
block empty. The counts and the enclosure of `restructure` still read off the
reduced set, `restructure_q` and `restructure_p` included.

CORA's four `reduce` variants differ in which generators they judge worth
keeping, ranking dependent factors by the volume their removal costs. The ranking
here is Girard's, from `reduce`; what it ranks is the only difference.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


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
