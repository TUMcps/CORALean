module

public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Where a bound comes from: weak duality

Give the constraints nonnegative weights and add them up. Each inequality only gets weaker when its
left side is replaced by its right, and each equality does not change at all, so whatever
functional the weights assemble is bounded by whatever number they assemble, for every feasible
point at once and with no appeal to an optimum. That is the whole trusted content of an LP bound:
a solver's dual solution is such a weighting, and a solver that returns a wrong one produces no
bound rather than a wrong one. Setting the objective to zero turns the same statement into a
certificate of infeasibility.

## Inputs
* `A` – inequality constraint functionals
* `b` – inequality right-hand sides
* `Ae` – equality constraint functionals
* `be` – equality right-hand sides
* `c` – objective functional
* `y` – weights of the inequalities
* `z` – weights of the equalities

## Hypotheses
* `hy` – the inequality weights are nonnegative
* `hc` – the objective is the weighted sum of the constraint functionals

## Output
* a bound on the objective over the feasible set, the weighted right-hand sides
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {m me : ℕ}

/-- The feasible set of `A x ≤ b`, `Ae x = be`, written out rather than named:
`Global` sees no set representations, and a halfspace description unfolds to
this. -/
def Feasible (A : Fin m → (α →ₗ[ℝ] ℝ)) (b : Fin m → ℝ)
    (Ae : Fin me → (α →ₗ[ℝ] ℝ)) (be : Fin me → ℝ) : Set α :=
  {x | (∀ i, A i x ≤ b i) ∧ ∀ i, Ae i x = be i}

theorem le_dual_bound (A : Fin m → (α →ₗ[ℝ] ℝ)) (b : Fin m → ℝ)
    (Ae : Fin me → (α →ₗ[ℝ] ℝ)) (be : Fin me → ℝ)
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    {x : α} (hle : ∀ i, A i x ≤ b i) (heq : ∀ i, Ae i x = be i) : -- --- CONCL ---
    (∑ i, y i * A i x) + (∑ i, z i * Ae i x)
      ≤ (∑ i, y i * b i) + ∑ i, z i * be i := by -- --- PROOF ---
  refine add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hy i)) ?_
  exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [heq i])


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dual solution `(y, z)` bounds every objective it assembles. The
hypothesis is the dual feasibility `c = yᵀA + zᵀAe`, stated pointwise because a
functional is determined by what it does. -/
def SupportBound.ofDual {A : Fin m → (α →ₗ[ℝ] ℝ)} {b : Fin m → ℝ}
    {Ae : Fin me → (α →ₗ[ℝ] ℝ)} {be : Fin me → ℝ} {c : α →ₗ[ℝ] ℝ}
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ x : α, c x = (∑ i, y i * A i x) + ∑ i, z i * Ae i x) :
    SupportBound (Feasible A b Ae be) c where
  val := (∑ i, y i * b i) + ∑ i, z i * be i
  le x hx := by
    rw [hc x]
    exact le_dual_bound A b Ae be y z hy hx.1 hx.2


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
