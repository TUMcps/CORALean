module

public import CORALean.ContDynamics.NonlinDASys.Theorems.MemLinInclusion

@[expose] public section

/-!
# A run of the DAE solves the abstracting inclusion

[1, Prop. 1]: if `L̄ ⊇ L`, the solution of the original dynamics is enclosed by the solution
of the abstracting differential inclusion `˙x̃ ∈ Ã x̃ ⊕ w ⊕ B̃ (U ⊕ (-u*)) ⊕ L̄`. Read as: a
run `(x, y, u)` of the system on `τ` has, at every time of `τ`, a derivative `ẋ(t)` in the
inclusion's right-hand side at `x(t) - x*` — it is a solution of the inclusion.

Two hypotheses carry what the printed proof assumes. The run stays in the region `R^z`
the errors are taken over: the proof quantifies over `x ∈ Rᵈ(τₖ)`, `y ∈ Rᵃ(τₖ)`, `u ∈ U`,
the sets being computed, and never shows the run stays there; the proposition's own
"independent of the amount of overapproximation" says the same. And `L̄` holds the exact
linearization error `ℓᵈ - C F⁻¹ ℓᵃ` at every consistent point of `R^z`, which is `L ⊆ L̄` with
`L` read with one Lagrange point per row ([1, Eq. 8]) rather than the single `ξ` of
[1, Eq. 15], which can miss it (`SharedLagrangePoint`).

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: a run confined to `R^z`, over which `L̄` holds every consistent point's
linearization error, has `ẋ(t) ∈ Ã (x(t) - x*) ⊕ w ⊕ B̃ (U ⊕ (-u*)) ⊕ L̄` on all of `τ`. -/
theorem NonlinDASys.Trajectory.hasDerivWithinAt_mem_linInclusion {sys : NonlinDASys n p m}
    {τ : Set ℝ} {R₀ : Set (Vec ℝ n)} {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p}
    {u : ℝ → Vec ℝ m} (hrun : sys.Trajectory (S := 𝒮) τ R₀ U x y u)
    {xs : Vec ℝ n} {ys : Vec ℝ p} {us : Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m}
    {C : Mat ℝ n p} {D : Mat ℝ p n} {E : Mat ℝ p m} {F F_inv : Mat ℝ p p}
    (hF : F_inv * F = 1) {L : Set (Vec ℝ n)} {Rz : Set (Vec ℝ n × Vec ℝ p × Vec ℝ m)}
    (hR : ∀ t ∈ τ, (x t, y t, u t) ∈ Rz)
    (hL : ∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      (sys.f x' y' u' - (sys.f xs ys us + A *ᵥ (x' - xs) + B *ᵥ (u' - us) + C *ᵥ (y' - ys)))
        - (C * F_inv) *ᵥ (sys.g x' y' u' - (sys.g xs ys us + D *ᵥ (x' - xs) + E *ᵥ (u' - us)
          + F *ᵥ (y' - ys))) ∈ L) :
    ∀ t ∈ τ, ∃ v ∈ NonlinDASys.linInclusion (sys.f xs ys us) (sys.g xs ys us) A B C D E F_inv
      us U L (x t - xs), HasDerivWithinAt x v τ t := by -- --- PROOF ---
  intro t ht
  -- the derivative is the field at the run's own point, which [1, Eq. 16] holds
  exact ⟨sys.f (x t) (y t) (u t),
    NonlinDASys.mem_linInclusion sys hF (hrun.input t ht) (hrun.constraint t ht)
      (hL _ _ _ (hR t ht) (hrun.constraint t ht)),
    hrun.flow t ht⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
