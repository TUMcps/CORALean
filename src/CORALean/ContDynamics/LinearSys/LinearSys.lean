import CORALean.ContSet.ContSet.ContSet

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`, reduced to `ẋ(t) = A x(t) + u(t)`: the class there is
`ẋ = A x + B u + c` with an output `y = C x + D u + k`, and here only `A` is kept,
the input entering in state coordinates as in [1, Sec. 3.2]. `B U ⊕ c` is one `mtimes` and
one `plus` on the input set, so the folded form reaches the same states.

The output equation is `OutputEq`, paired with a computed set rather than stored
here, because `discretize` hands `LinearSysDT` an input set of state
contributions over a step and not of inputs: a `D` stored on either system would
multiply the wrong set at one of them.

The time domain `T` is a parameter — `Set.Ici 0` for all forward time,
`Set.Icc 0 τ` for a bounded horizon — and the derivative is taken within `T`
itself, two-sided wherever `T` is: within `Ici t` it would be a right derivative
everywhere, which does not force continuity, and a run free to jump is not a
trajectory. `init` stays unconditional, and `u` needs no regularity, being
pinned by `u t = ẋ(t) - A x(t)` wherever the flow holds.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSys (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSys.Trajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
