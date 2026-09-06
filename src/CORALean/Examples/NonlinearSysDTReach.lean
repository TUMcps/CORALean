import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn
import CORALean.ContSet.Interval.Real.Instances

/-!
# Reachability of a discrete nonlinear system

`NonlinearSysDT` at `f(x, u) = x² + u`, one state and one input, so the
linearization at any point `p` has no truncation error at all: `f`'s own
second-order term is exact, so subtracting the affine part at `p` leaves
exactly `(x - p)²`, a computed quantity rather than a bounded one. Bounding it
over `|x - p| ≤ r` is then `sq_le_sq'`, not an estimate.

`Interval` is the representation: `NonlinearSysDT.reach` asks for `Plus`,
`Reduce`, `Mtimes (Mat ℝ)` and `OfInterval`, and a box has the first three
verbatim and the fourth as the identity.

Nothing here evaluates to a number: `NonlinearSysDT` carries no scalar
parameter the way `LinearSysDT` does — its certificate's `A` is real, per the
issue that landed it — so, as in `NeurNetControl.lean`, every operation stays
over ℝ and `def` would still be `noncomputable`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

/-- The step `x ↦ x² + u`, the simplest map whose linearization error is exact
rather than merely bounded. -/
def Example.quadraticStep : NonlinearSysDT 1 1 where
  f x u := ![x 0 ^ 2 + u 0]

/-- The tangent slope at `p`: `f`'s own second derivative, `2`, is what makes
the residual below `(x - p)²` and nothing more. `Matrix.of` rather than `!!`,
so an entry unfolds by `Matrix.of_apply` and not a chain of `cons` lemmas. -/
def Example.quadraticA (p : ℝ) : Mat ℝ 1 1 := Matrix.of fun _ _ => 2 * p

/-- The input enters affinely, so its coefficient is exact at every point. -/
def Example.quadraticB : Mat ℝ 1 1 := Matrix.of fun _ _ => 1

/-- The region a certificate is issued over: within `r` of the expansion
point. -/
def Example.quadraticRegion (p r : ℝ) : Set (Vec ℝ 1) := {x | |x 0 - p| ≤ r}

/-- `(x - p)²` ranges over `[0, r²]` on the region above, so this is the whole
enclosure, not a widened one. -/
def Example.quadraticL (r : ℝ) : Interval (Vec ℝ 1) := ⟨![0], ![r ^ 2]⟩

/-- The certificate: arithmetic, since the residual is a computed square rather
than a Taylor remainder. -/
theorem Example.quadraticCert (p q r : ℝ) (U : Interval (Vec ℝ 1)) :
    AbstractionError (S := fun n => Interval (Vec ℝ n)) Example.quadraticStep.f
      (Example.quadraticA p) Example.quadraticB ![p] ![q] (Example.quadraticRegion p r)
      (construct U) (Example.quadraticL r) where
  encloses x hx u _ := by
    intro i
    -- `n = 1`, so the only coordinate is `0`
    rw [show i = 0 from Subsingleton.elim i 0, Entrywise.entry_vec, Entrywise.entry_vec]
    -- the split leaves exactly the quadratic term, `u` and `q` cancelling
    have heq : (Example.quadraticStep.f x u
        - (Example.quadraticStep.f ![p] ![q]
          + Example.quadraticA p *ᵥ (x - ![p])
          + Example.quadraticB *ᵥ (u - ![q]))) 0 = (x 0 - p) ^ 2 := by
      simp only [Example.quadraticStep, Example.quadraticA, Example.quadraticB,
        Pi.sub_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
        Matrix.of_apply, Matrix.cons_val_zero]
      ring
    have hb := abs_le.mp (show |x 0 - p| ≤ r from hx)
    rw [heq]
    exact ⟨sq_nonneg _, sq_le_sq' (by linarith [hb.1]) hb.2⟩

/-- One linearization at `p`, over the box representation. -/
def Example.quadraticLinStep (p q r : ℝ) (U : Interval (Vec ℝ 1)) :
    Example.quadraticStep.LinStep (S := fun n => Interval (Vec ℝ n)) U where
  A := Example.quadraticA p
  B := Example.quadraticB
  xs := ![p]
  us := ![q]
  R := Example.quadraticRegion p r
  L := Example.quadraticL r
  cert := Example.quadraticCert p q r U

-- anonymous, since their content is that `reach_outer` applies with a real certificate

/-- Every trajectory lies in `reach` at every step, the same linearization
reused throughout — `reach_outer` asks for nothing else once the certificate is
in hand. -/
example (p q r : ℝ) (U R₀ : Interval (Vec ℝ 1)) (o : ℕ) {x u : ℕ → Vec ℝ 1}
    (traj : Example.quadraticStep.Trajectory (S := fun n => Interval (Vec ℝ n)) R₀ U x u)
    (hR : ∀ k, x k ∈ Example.quadraticRegion p r) (k : ℕ) :
    x k ∈ construct (Example.quadraticStep.reach (S := fun n => Interval (Vec ℝ n)) o
      (fun _ => Example.quadraticLinStep p q r U) R₀ k) :=
  Example.quadraticStep.reach_outer o (fun _ => Example.quadraticLinStep p q r U) R₀ traj hR k

/-- The bounded-horizon form, for a run known only up to step `K`. -/
example (p q r : ℝ) (U R₀ : Interval (Vec ℝ 1)) (o K : ℕ) {x u : ℕ → Vec ℝ 1}
    (traj : Example.quadraticStep.TrajectoryOn (S := fun n => Interval (Vec ℝ n))
      R₀ U K x u)
    (hR : ∀ k < K, x k ∈ Example.quadraticRegion p r) (k : ℕ) (hk : k ≤ K) :
    x k ∈ construct (Example.quadraticStep.reach (S := fun n => Interval (Vec ℝ n)) o
      (fun _ => Example.quadraticLinStep p q r U) R₀ k) :=
  Example.quadraticStep.reach_outer_on o (fun _ => Example.quadraticLinStep p q r U) R₀ traj hR k
    hk

end CORALean.Real
