import CORALean.ContDynamics.NonlinDASys.NonlinDASys

/-!
# A reduced model of a differential-algebraic system

The algebraic variable as a function of the state and the input: `h` with `g(x, h(x,u), u) = 0`
(`sound`) and the only solution of the constraint (`unique`). `unique` is what a global solve
of an index-1 system gives and what the implicit function theorem gives only locally,
`NonlinDASys.localReduction`, so a model is data the caller supplies, as a certificate is.
It is exactly what lets `y` be eliminated: a trajectory's `y` is `h (x t) (u t)`, so the
trajectories of the system are those of the ordinary system `ẋ = f(x, h(x,u), u)`
(`NonlinDASys.ReducedModel.toNonlinearSys`), with no run lost and none added.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n p m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinDASys.ReducedModel (sys : NonlinDASys n p m) where
  h : Vec ℝ n → Vec ℝ m → Vec ℝ p
  sound (x : Vec ℝ n) (u : Vec ℝ m) : sys.g x (h x u) u = 0
  unique (x : Vec ℝ n) (y : Vec ℝ p) (u : Vec ℝ m) : sys.g x y u = 0 → y = h x u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
