module

public import CORALean.ContSet.Taylm.Real.Definitions.CodeList

@[expose] public section

/-!
# A code list with its constants converted

What lets the float layer's code lists, whose constants are floats, be read as real ones for
[1, Thm. 3]: the same list, each constant through `φ`.

## Inputs
* `α` – source constant type
* `β` – target constant type
* `m` – number of variables
* `φ` – constant conversion

## Output
* code list with its constants converted

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.CodeList.map {α β : Type} {m : ℕ} (φ : α → β) :
    Taylm.CodeList α m → Taylm.CodeList β m
  | .var i => .var i
  | .const c => .const (φ c)
  | .add a b => .add (a.map φ) (b.map φ)
  | .mul a b => .mul (a.map φ) (b.map φ)
  | .neg a => .neg (a.map φ)
  | .intr s a => .intr s (a.map φ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
