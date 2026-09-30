import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.SetUnion.SetUnion

/-!
# One reachability interface, over every system class

CORA's `reach(sys, params, options)`, read as a class the way `Mtimes` and
`Enclose` are. `reachExact sys params` is what the dynamics reach, a `Set` nothing
may widen; `reach sys params options` is what an algorithm computes for it, `none`
where it could not certify its soundness conditions at run time — CORA's failure
mode, as when a linearization region misses the set computed in it, or a horizon is
no multiple of `timeStep`. `reach_outer` encloses the first in every result.

`P n` is CORA's `params`, the problem: `R0`, the horizon `[tStart, tFinal]`, and `U`
where the system does not bind its input set itself — `Reach.Params` or
`Reach.InputParams` at the family's time type, which is `P`'s business and no
parameter of the class. `O` is CORA's `options`, the algorithm. `reachExact` takes
no options: what a system reaches does not depend on how it is enclosed. Both are
`outParam`s, as CORA's `reach` dispatches on the class of `sys` alone: one instance
per system class and representation fixes them, `⟨R₀, 0, 1⟩` elaborates against it,
and `reachExact`, which never mentions `O`, still resolves. `Sys` may sit in
`Type 1`, as a closed loop storing a `NeuralNetwork` does.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `reachExact sys params` is the exact set the problem `params` asks for; `reach sys params
options` is what an algorithm computes for it, `none` if it could not certify itself;
`reach_outer` is the enclosure between them, at every result `reach` returns. -/
class Reach (Sys : ℕ → Type u) (P : outParam (ℕ → Type)) (O : outParam Type) (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] where
  reachExact {n : ℕ} : Sys n → P n → Set (Vec ℝ n)
  reach {n : ℕ} : Sys n → P n → O → Option (SetUnion (S n))
  reach_outer {n : ℕ} (sys : Sys n) (params : P n) (options : O) :
    match reach sys params options with
    | some R => reachExact sys params ⊆ construct R
    | none => True

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
