module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# One entry of a stencil matrix

An entry of a stencil matrix is one kernel weight or zero. Written as `∑ l, if tap j l = i then w j
l else 0` that is `k` additions, which a machine scalar rounds, so the matrix read back into ℝ would
be the convolution only approximately; written as a recursion that stops at the first tap reading
`i`, it is a *placement*: no arithmetic is consulted, and `toReal_tapEntry` is an equality with no
hypothesis. `step_tapEntryImpl` is the same scan as a loop, swapped in by `@[csimp]` for what runs;
`Fin.foldr` nests to the right, so the *first* tap reading `i` still wins.

## Inputs
* `n` – number of inputs

## Output
* weight of the first tap reading the input, or zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The same scan as a loop. -/
@[step_of tapEntry]
def step_tapEntryImpl {n k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (i : Fin n) : 𝕋 :=
  Fin.foldr k (fun l acc => if t l = i then v l else acc) zero


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The weight one row places at input coordinate `i`: the first tap reading it, and `zero`
if none does. -/
def tapEntry {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Fin k → 𝕋) → Fin n → 𝕋
  | 0, _, _, _ => zero
  | _ + 1, t, v, i =>
    if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
