module

public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane
public import CORALean.ContSet.Conversion.Float.Instances

@[expose] public section

/-!
# CORA's `projectOnHyperplane`, over a floating-point scalar

`(I - c cᵀ) S + d c` for the hyperplane `{x | c ⬝ x = d}`, the normal and offset floats. Their
products round, so the projector is an interval matrix, each entry `δᵢⱼ - cᵢ cⱼ` bracketed by
directed arithmetic, and the translation `d c` is a box; the set goes through `mtimes` at the
interval matrix, then `plus` with the box taken into the representation (`ofInterval`).

## Inputs
* `s` – set
* `c` – unit normal
* `d` – hyperplane offset

## Output
* `s` projected onto the hyperplane `{x | c ⬝ x = d}`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float FloatOps SoundFloatArithmetic
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ[𝕋] S]
variable [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def ContSet.projectOnHyperplaneFloat (s : S n) (c : Vec 𝕋 n) (d : 𝕋) : S n :=
  -- the projector `I - c cᵀ`, each entry bracketed
  let A : Interval (Mat 𝕋 n n) :=
    ⟨fun i j => subDown (if i = j then one else zero) (mulUp (c i) (c j)),
      fun i j => subUp (if i = j then one else zero) (mulDown (c i) (c j))⟩
  -- the translation `d c`, bracketed
  let b : Interval (Vec 𝕋 n) := ⟨fun i => mulDown d (c i), fun i => mulUp d (c i)⟩
  Plus.plus (Mtimes.mtimes (𝕄 := ℐ[𝕋]) A s) (OfInterval.ofInterval b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
