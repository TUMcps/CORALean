module

public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# One reachability interface, over every system class

CORA's `reach(sys, params, options)`, read as a class the way `Mtimes` and `Enclose` are.
`reachExact sys params` is what the dynamics reach, a `Set` nothing may widen; `reach sys
params options` is what an algorithm computes for it, `none` where it could not certify its
soundness conditions at run time, where CORA raises an error: a linearization region missing
the set computed in it, a horizon no multiple of `Δt`. `reach_outer` encloses the first in a set
`reach` returned, taken by `reach … = some R`: a failed run has no `R`, its hypothesis is
`none = some R`, which is `False`, and nothing follows. What the run can decide it tests before
returning `some`; a positive zonotope order, where `options` carries it, is a field with a
default proof, refused at elaboration as CORA's `validateOptions` refuses it.

`P n` is CORA's `params`, the problem: `X₀` (its `R0`), the horizon `[tStart, tFinal]`, and `U`
where the system does not bind its input set itself — `Reach.Params` or `Reach.InputParams` at
the family's time type. `O` is CORA's `options`, the algorithm; `reachExact` takes none, as what
a system reaches does not depend on how it is enclosed. Both are `outParam`s, as CORA's `reach`
dispatches on the class of `sys` alone, so `reachExact`, which never mentions `O`, resolves.
`Sys` may sit in `Type 1`, as a closed loop storing a `NeuralNetwork` does.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `reachExact sys params` is the exact set the problem `params` asks for; `reach sys params
options` is what an algorithm computes for it, `none` if it could not certify itself;
`reach_outer` is the enclosure between them, at a set `reach` returned and at nothing else. -/
class Reach (Sys : ℕ → Type u) (P : outParam (ℕ → Type)) (O : outParam Type) (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] where
  reachExact {n : ℕ} : Sys n → P n → Set (Vec ℝ n)
  reach {n : ℕ} : Sys n → P n → O → Option (SetUnion (S n))
  reach_outer {n : ℕ} (sys : Sys n) (params : P n) (options : O) {R : SetUnion (S n)}
    (h : reach sys params options = some R) : reachExact sys params ⊆ construct R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
