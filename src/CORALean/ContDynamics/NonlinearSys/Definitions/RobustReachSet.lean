import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# Maximal, minimal and robust reachable sets

[1, Sec. III]: for `ż = f(z, u)` with solution `φ(t; z₀, u)`, the robustly reachable set
`R_AE(t; Z₀, U) = {z | ∀u_A ∈ U_A, ∃u_E ∈ U_E, ∃z₀ ∈ Z₀, z = φ(t; z₀, (u_A, u_E))}`: the
disturbance part `u_A` of the input universally quantified, the control part `u_E`
existentially. The maximal reachable set `R_E` is the case of a single disturbance signal,
the minimal one `R_A` that of a single control signal.

[1] assumes a unique solution for every initial state and input signal, so the solution
map `φ` is an argument; the admissible signals — [1]'s piecewise constant ones with
finitely many discontinuities — are the sets `UA` and `UE`.

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n pA pE : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. III]: the states reached at `t` from `Z₀` for every disturbance signal in `UA`
by some control signal in `UE`. -/
def NonlinearSys.robustReachSet
    (φ : ℝ → Vec ℝ n → (ℝ → Vec ℝ pA) → (ℝ → Vec ℝ pE) → Vec ℝ n) (Z₀ : Set (Vec ℝ n))
    (UA : Set (ℝ → Vec ℝ pA)) (UE : Set (ℝ → Vec ℝ pE)) (t : ℝ) : Set (Vec ℝ n) :=
  {z | ∀ uA ∈ UA, ∃ uE ∈ UE, ∃ z₀ ∈ Z₀, z = φ t z₀ uA uE}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
