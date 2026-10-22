module

public import CORALean.NN.Layers.Interfaces

@[expose] public section

/-!
# What a layer is

CORA's `nnLayer`, split in two: `Layer` is what a layer *computes* on a set, and `Layer.Encloses`
(in `Definitions/Basic.lean`) the obligation tying it to an exact function, [1, Prop. 2.14]. No
field of `Layer` mentions `ℝ`: a structure with a noncomputable field is noncomputable to construct,
so every mention of `ℝ` lives in a `Prop` and a float layer is a plain `def`. A layer is a
structure, not a class: a network holds many, told apart by their weights. The class is one level
up, per *kind*, `Enclose` in `Interfaces.lean`; `Enclose.toLayer` (in `Operations/Basic.lean`)
forgets the kind.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- A layer as what it computes on a set: a propagation from sets of dimension `n` to sets of
dimension `m`. -/
structure Layer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  enclose : S n → S m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
