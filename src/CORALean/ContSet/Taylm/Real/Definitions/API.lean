module

public import CORALean.ContSet.Taylm.Real.Definitions.Basic
public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import CORALean.ContSet.Taylm.Real.Definitions.CodeList
public import CORALean.ContSet.Taylm.Real.Definitions.CodeScale
public import CORALean.ContSet.Taylm.Real.Definitions.IsGoodBox
public import CORALean.ContSet.Taylm.Real.Definitions.IsTaylorModel
public import CORALean.ContSet.Taylm.Real.Definitions.IsScaled
public import CORALean.ContSet.Taylm.Real.Definitions.TaylorModelOn

/-!
# What a Taylor model means beyond its own construction

`IsTaylorModel` is [1, Def. 1]: a model whose polynomial is the Taylor polynomial, which
`Encloses` does not ask. `IsScaled` is the `(n+1)`-st order scaling of [1, Thm. 1], read over the
normalized box. `CodeList` is what [1, Thm. 2] inducts over, and `codeScale` the constant a code
list's run is scaled by. `TaylorModelOn` is a model over an explicit, unnormalized box domain.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/
