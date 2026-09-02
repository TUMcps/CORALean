import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter

/-!
# What `ConZonotope` instantiates

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- At every ambient type, not only `Vec`: the constraints live on the
coefficient space whatever the generators point into. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (ConZonotope α) α :=
  ⟨ConZonotope.construct⟩

instance : Plus (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := ConZonotope.plus
  plus_outer C₁ C₂ := (ConZonotope.plus_exact C₁ C₂).subset

/-- Relaxed to the enclosing zonotopes, which is the one operation a constrained
zonotope does not compute in its own terms. Now a separate instance, so a caller
that never combines does not depend on the relaxation. -/
noncomputable instance : LinComb (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

noncomputable instance : Reduce (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => ConZonotope (Vec ℝ n)) where
  mtimes := ConZonotope.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (ConZonotope.mtimes_exact M C).subset

/-- The constrained-zonotope family over vectors. A generic theorem quantifies
over `S : ℕ → Type` and the elaborator cannot read that family off one member, so
a use site has to name it: `(S := 𝒞)`. -/
scoped notation "𝒞" => fun n => ConZonotope (Vec ℝ n)

/-- The same operation at an interval matrix, which a discretization wants and
no other class asks for. This is the last instance `LinearSys`
reachability needs, so a constrained zonotope now runs it. -/
noncomputable instance : Mtimes ℐ 𝒞 where
  mtimes := ConZonotope.mtimesIntervalMat
  mtimes_outer IM C := ConZonotope.mtimesIntervalMat_outer IM C

end CORALean.Real
