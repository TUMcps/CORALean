import CORALean.ContDynamics.NonlinDASys.Operations.Reach
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachLoopOuter

/-!
# [1, Alg. 1] holds every certified run

The union `Rᵈ([0, t_f])` that `reach` returns holds every state a run of the DAE from `Rᵈ(0)`
takes on `[0, t_f]`, as long as the run is certified at every step by the errors the loop
computes: stays in the region over which [1, Cor. 1] bounds the linearization errors, which is
[1, Prop. 1]'s assumption and which `[1]`'s proof does not establish. The horizon is `K` steps, a
whole number, and positive: at `t_f = 0` the loop does not run and the union is empty.
`reachLoop_outer` is the induction; here it is started at `t_0 = 0`, `L = {0}` and `R_union = ∅`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: a run certified at every step is in the union `Rᵈ([0, t_f])` that `reach`
returns, for a horizon of `K ≥ 1` steps. -/
theorem NonlinDASys.reach_outer (sys : NonlinDASys n p m)
    (taylor : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (hsub : ∀ {k : ℕ} (A B : Zonotope (Vec ℝ k)), sub A B = true → A.construct ⊆ B.construct)
    (splitFn : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
    (hsplit : ∀ Z, Z.construct ⊆ (splitFn Z).1.construct ∪ (splitFn Z).2.construct)
    (Lmax : Zonotope (Vec ℝ n)) (lam : ℝ) {r : ℝ} (hr : 0 < r) {q : ℕ}
    (U : Zonotope (Vec ℝ m)) {R0 : Zonotope (Vec ℝ n)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p}
    {u : ℝ → Vec ℝ m} {K : ℕ} (hK : 0 < K)
    (traj : sys.Trajectory (S := 𝒵) (Set.Icc 0 ((K : ℝ) * r)) R0 U x y u)
    (hcert : ∀ j : ℕ, j < K → ∀ (fuel : ℕ) (Z : Zonotope (Vec ℝ n))
      (L₀ : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)) (rr : NonlinDASys.ErrorLoopResult n p),
      x ((j : ℝ) * r) ∈ Z.construct →
      NonlinDASys.reachRepeat sys (taylor Z) corollary1 sub Lmax lam r (q + 2) Z U fuel L₀
        = some rr →
      ({ taylor Z with Verror := rr.L.1, Verror_y := rr.L.2 } :
        NonlinDASys.LinPoint n p m).Certifies
        sys U r q (fun s => x ((j : ℝ) * r + s)) (fun s => y ((j : ℝ) * r + s))
        (fun s => u ((j : ℝ) * r + s)))
    (fuel : ℕ) {res : Set (Vec ℝ n)}
    (h : sys.reach taylor corollary1 sub splitFn R0 ((K : ℝ) * r) r U Lmax lam (q + 2) fuel
      = some res) :
    ∀ t ∈ Set.Icc 0 ((K : ℝ) * r), x t ∈ res := by -- --- PROOF ---
  intro t ht
  have := sys.reachLoop_outer taylor corollary1 sub hsub Lmax lam hr U splitFn hsplit traj hcert
    fuel 0 K 0 0 ((K : ℝ) * r) R0 _ ∅ (by simp) rfl (Nat.zero_le _) (by omega) hK
    (by simp only [Nat.add_zero, Nat.cast_zero, zero_mul]; exact traj.init)
    (fun h => absurd h (lt_irrefl 0)) res h t ht
  simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
