module

public import CORALean.ContSet.HPolytope.Real.Operations.BoundOfDual
public import CORALean.Global.LinProg.Simplex

@[expose] public section

/-!
# `HPolytope.supportBound`

The bound a halfspace description can answer for itself, and the reason it can:
`Simplex` proposes a weighting of the rows, this file *checks* it and hands the
check to `boundOfDual`. A weighting that fails either test yields `none`, so the
solver is not trusted with anything — replacing it by a random number generator
would lose every bound and no theorem.

An equality row is two inequalities, `Ae x ≤ be` and `-Ae x ≤ -be`, so the free
dual variable comes back as the difference of two nonnegative ones and the
solver never has to know that equalities exist.

At `Vec ℝ n` alone: the simplex reads coefficients, and a functional only has
those once there are coordinates. Noncomputable, and unavoidably so at this
layer — whether two reals are equal is not decidable, so neither is whether a
weighting reproduces `c`. `Float` is where this same bridge runs.

The linear program [1, Def. 3] names, with the dual solution kept as a reason.

## Inputs
* `P` – H-polytope
* `c` – center of length `n →ₗ[ℝ] ℝ`

## Output
* a bound in direction `c`, or `none` where no weighting passed the checks

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A functional's coordinates, read off the standard basis: the simplex sees
numbers, never maps. -/
def aux_coeff (f : Vec ℝ n →ₗ[ℝ] ℝ) (j : Fin n) : ℝ := f fun k => if k = j then 1 else 0

/-- The inequality system the simplex is given: the rows, then each equality
row twice with opposite signs. -/
def aux_ineqs (P : HPolytope (Vec ℝ n)) : Fin (P.m + (P.me + P.me)) → Fin n → ℝ :=
  Fin.append (fun i => aux_coeff (P.A i))
    (Fin.append (fun i => aux_coeff (P.Ae i)) fun i j => -aux_coeff (P.Ae i) j)

/-- The right-hand sides matching `aux_ineqs`. -/
def aux_rhs (P : HPolytope (Vec ℝ n)) : Fin (P.m + (P.me + P.me)) → ℝ :=
  Fin.append P.b (Fin.append P.be fun i => -P.be i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A bound in direction `c`, or `none` where no weighting passed the checks
below — an unbounded description, or a pivot budget, linear in the problem
size, that ran out. -/
noncomputable def HPolytope.supportBound (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    Option (SupportBound P.construct c) :=
  match dualCandidate (64 * (P.m + P.me + P.me + n + 1)) (aux_ineqs P) (aux_rhs P)
      (aux_coeff c) with
  | none => none
  | some w =>
    -- the equality rows' two weights recombine into the one free dual variable
    let y : Fin P.m → ℝ := fun i => w (Fin.castAdd _ i)
    let z : Fin P.me → ℝ := fun i =>
      w (Fin.natAdd P.m (Fin.castAdd _ i)) - w (Fin.natAdd P.m (Fin.natAdd P.me i))
    if h : (∀ i, 0 ≤ y i) ∧ ∀ x : Vec ℝ n, c x = (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x then
      some (P.boundOfDual y z h.1 h.2)
    else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
