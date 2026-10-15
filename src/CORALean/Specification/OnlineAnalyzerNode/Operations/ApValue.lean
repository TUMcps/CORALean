module

public import CORALean.Specification.AtomicProposition.Operations.CanBeFalse
public import CORALean.Specification.AtomicProposition.Operations.CanBeTrue
public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# The Kleene value of an atomic proposition on a set

The branch of `observeSet` for an `AP` node that turns `canBeTrue` and `canBeFalse` into a value:
`True` if the proposition can only be true, `False` if it can only be false, `Unknown` if it can
be both, and an error if it can be neither (`CORA:notDefined`, "AP can neither be true nor
false"), here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `val` of `observeSet`, from `obj.ap.canBeTrue(set,loc)` and `obj.ap.canBeFalse(set,loc)`. -/
def OnlineAnalyzerNode.apValue (ap : AtomicProposition S d) (set : S d) (loc : ℕ) :
    Option Kleene :=
  match ap.canBeTrue (𝕋 := 𝕋) set loc, ap.canBeFalse (𝕋 := 𝕋) set loc with
  | true, false => some .tt
  | false, true => some .ff
  | true, true => some .uu
  | false, false => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
