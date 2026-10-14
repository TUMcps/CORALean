module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Interval

@[expose] public section

/-!
# `intPrev & interval(lo,hi)` for extended bounds

The real-layer `Interval` has no infinite bound; where CORA intersects `intPrev` with an interval
that
has one (`log(0) = -Inf`, `atanh(1) = Inf`, `tan(pi/2) = Inf`), the bound clips to `intPrev`'s. An
upper
bound `-Inf` (or a lower one `+Inf`) leaves the empty interval, `[inf, inf - 1]`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intPrev & interval(lo,hi)` for bounds in `EReal`. -/
noncomputable def SyntaxTree.restrict (prev : Dom) (lo hi : EReal) : Dom :=
  ⟨fun _ => (max (prev.inf 0 : EReal) lo).toReal,
    fun _ => if hi = ⊥ then prev.inf 0 - 1 else (min (prev.sup 0 : EReal) hi).toReal⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
