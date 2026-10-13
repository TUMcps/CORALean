module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# One step of the re-linearization loop

A single linearization is `AbstractionError` together with the matrices and the
expansion point it was issued for. Bundling them is what makes a *sequence* of
linearizations sayable: seven parallel families indexed by the step count is not
a statement anyone can read, and the certificate has to travel with the data it
certifies or the wrong `L` reaches the wrong `A`.

A chain of steps is a function `ℕ → LinStep`: `relinReach` recurses on the step
index and looks nothing up, the composition theorem is `Nat.rec` with one
hypothesis family `∀ i < N` per obligation, and a chain longer than the horizon
costs nothing. Not an inductive chain as `HybridAutomaton.Run` is: a hybrid run is
a datum of the *system*, a chain of linearizations one of the *analysis*, and
inductive would put the enclosures inside the proof.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization of `sys`, with the certificate that makes it conservative
wherever the state stays in `R`. -/
structure NonlinearSys.LinStep (sys : NonlinearSys n m) (U : S m) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  xs : Vec ℝ n
  us : Vec ℝ m
  R : Set (Vec ℝ n)
  L : S n
  cert : AbstractionError sys.f A B xs us R (construct U) L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
