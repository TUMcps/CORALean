import CORALean.ContSet.ContSet.ContSet

/-!
# Nonlinear ARX models: the representation

CORA's `nonlinearARX` [1], `y(k) = f(y(k-1), …, y(k-p), u(k), …, u(k-p))`, in the
outputs and not in a state, with `f` over `ℝ` as `NonlinearSysDT` holds its `f`.
`f` takes the past outputs stacked as CORA documents them, block `i` of the first
argument holding `y(k-1-i)`, and the inputs, block `j` of the second holding
`u(k-j)`; `pastOut` and `pastIn` read those two windows off a signal.

Time is counted in sampling periods, as in `NonlinearSysDT`, so no `dt` is stored.
Left out: CORA's cached Jacobian, Hessian and third-order tensor, which
`NonlinearSysDT.LinStep` already supplies at the converted system.

`stack y k` is the window `(y(k), …, y(k+p-1))`, block `a` holding `y(k+a)`, the
state the conversion to `NonlinearSysDT` carries. `Trajectory` is the ARX
recursion for every `k ≥ p`, the first window `stack y 0` in `Y₀` as CORA's `y0`,
and every input in `U`; the conversion is not used to state it.

## References

* [1] `contDynamics/@nonlinearARX/nonlinearARX.m`
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinearARX (dy du p : ℕ) where
  f : Vec ℝ (p * dy) → Vec ℝ ((p + 1) * du) → Vec ℝ dy

/-- The window of `p` outputs starting at `k`, block `a` holding `y(k+a)`. -/
def NonlinearARX.stack (p : ℕ) (y : ℕ → Vec ℝ dy) (k : ℕ) : Vec ℝ (p * dy) :=
  fun r => y (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

/-- The past outputs `(y(k-1), …, y(k-p))` at step `k`, block `i` holding `y(k-1-i)`. -/
def NonlinearARX.pastOut (p : ℕ) (y : ℕ → Vec ℝ dy) (k : ℕ) : Vec ℝ (p * dy) :=
  fun r => y (k - ((finProdFinEquiv.symm r).1 + 1)) (finProdFinEquiv.symm r).2

/-- The inputs `(u(k), …, u(k-p))` at step `k`, block `j` holding `u(k-j)`. -/
def NonlinearARX.pastIn (p : ℕ) (u : ℕ → Vec ℝ du) (k : ℕ) : Vec ℝ ((p + 1) * du) :=
  fun r => u (k - (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

structure NonlinearARX.Trajectory (sys : NonlinearARX dy du p) (Y₀ : S (p * dy)) (U : S du)
    (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du) : Prop where
  init : NonlinearARX.stack p y 0 ∈ construct Y₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) (hk : p ≤ k) :
    y k = sys.f (NonlinearARX.pastOut p y k) (NonlinearARX.pastIn p u k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
