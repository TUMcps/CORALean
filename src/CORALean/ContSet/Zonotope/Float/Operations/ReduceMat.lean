module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Float.Operations.Unvec
public import CORALean.ContSet.Zonotope.Float.Operations.Vec

@[expose] public section

/-!
# `Zonotope.reduceMat`, over a floating-point scalar

CORA's `@matZonotope/reduce` with the method `girard`, as it is meant to run: the matrix zonotope
stacked column by column (`zonotope(matZ)`), reduced by Girard's method [1, Sec. 3.4] to the order
`o` in the `n * m` stacked dimensions, and unstacked into an `m × n` matrix zonotope again. CORA's
own code stops on the documented call, and with four arguments returns the wrong shape
(`Real.Zonotope.reduceMatCora`); stacking and unstacking move entries only, so the rounding is that
of `reduceGirard`.

## Inputs
* `Z` – matrix zonotope
* `o` – target order of the stacked zonotope

## Output
* matrix zonotope with at most `o * n * m` generators that encloses `Z`

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `matZonotope(reduce(zonotope(matZ), 'girard', o))`, in the shape of `Z`. -/
def Zonotope.reduceMat (Z : Zonotope (Mat 𝕋 m n)) (o : ℕ) : Zonotope (Mat 𝕋 m n) :=
  let V := Z.vec                                                -- `zonotope(matZ)`
  let R := V.reduceGirard o                                     -- `reduce(·, 'girard', o)`
  R.unvec                                                       -- back to `m × n`

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
