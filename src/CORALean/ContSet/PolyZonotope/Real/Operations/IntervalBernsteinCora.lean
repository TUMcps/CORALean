module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `PolyZonotope.intervalBernsteinCora`: `interval(pZ, 'bernstein')` as CORA's code runs

`@polyZonotope/interval.m` (l. 68-74), method `'bernstein'`:

```
B = poly2bernstein(pZ.G,pZ.E,dom);
infi = cellfun(@(x) min(min(x)),B);
```

`poly2bernstein` ends with `if h == 1, B = A{1}; else B = A; end` (`h = size(G,1)`, the
dimension), so it returns a matrix for a one-dimensional polynomial zonotope, and `cellfun` raises
"Input #2 expected to be a cell array". Reached by `interval(polyZonotope(0,1,[],2),'bernstein')`
and any one-dimensional `pZ` with a dependent generator and a factor (the generatorless case is not
modelled). Read from the source, not run. `none` is the MATLAB error; a normal return is `some ()`,
its value not modelled.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether CORA's `interval(pZ, 'bernstein')` returns (`some ()`) or errors (`none`). -/
def PolyZonotope.intervalBernsteinCora (pZ : PolyZonotope (Vec ℝ n)) : Option Unit :=
  -- h = size(G,1) == 1: poly2bernstein returns a matrix, and `cellfun` needs a cell
  if n = 1 ∧ 0 < pZ.h ∧ 0 < pZ.p then none else some ()

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
