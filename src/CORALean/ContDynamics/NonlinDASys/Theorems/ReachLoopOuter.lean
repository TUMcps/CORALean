module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachLoop
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinPointCertifiesOfSubset
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachRepeatSpec
public import CORALean.ContDynamics.NonlinDASys.Theorems.IsTrajectoryShift

@[expose] public section

/-!
# The time loop of [1, Alg. 1] holds every certified run

The run `x` of the DAE on `[0, K r]`, certified at every step by the errors the error loop
computes (`LinPoint.Certifies`, the hypotheses of `linReach_outer`), is in the union that
`reachLoop` returns. By induction on the fuel, on a state `(t_k, Rᵈ(t_k), R_union)` with the
run's state at `t_k` in `Rᵈ(t_k)` and everything before `t_k` in `R_union`: a step takes the run
from `t_k` to `t_{k+1}` (`linReach_outer` on the run counted from `t_k`, `TrajectoryShift`), its
`Rᵈ(τ_k)` joins the union, and a split puts the run's state in one half, which the recursive
call, from `t = 0` and horizon `t_f - t_k`, holds by the induction hypothesis. The run is counted
from an offset `k₀ r` so that the recursion's relative time is the run's absolute time.
`t_f = N r` and `t_k = k r`: the horizon is a whole number of steps, which `[1]` does not say.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] lines 2-23: a run certified at every step is in the union `reachLoop` returns,
from a state with the run's state in `Rk` and everything before `t_k` in `Runion`. -/
theorem NonlinDASys.reachLoop_outer (sys : NonlinDASys n p m)
    (taylor : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (hsub : ∀ {k : ℕ} (A B : Zonotope (Vec ℝ k)), sub A B = true → A.construct ⊆ B.construct)
    (Lmax : Zonotope (Vec ℝ n)) (lam : ℝ) {r : ℝ} (hr : 0 < r) {q : ℕ}
    (U : Zonotope (Vec ℝ m))
    (splitFn : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
    (hsplit : ∀ Z, Z.construct ⊆ (splitFn Z).1.construct ∪ (splitFn Z).2.construct)
    {R0 : Zonotope (Vec ℝ n)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m} {K : ℕ}
    (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 ((K : ℝ) * r)) R0 U x y u)
    (hcert : ∀ j : ℕ, j < K → ∀ (fuel : ℕ) (Z : Zonotope (Vec ℝ n))
      (L₀ : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)) (rr : NonlinDASys.ErrorLoopResult n p),
      x ((j : ℝ) * r) ∈ Z.construct →
      NonlinDASys.reachRepeat sys (taylor Z) corollary1 sub Lmax lam r (q + 2) Z U fuel L₀
        = some rr →
      ({ taylor Z with Verror := rr.L.1, Verror_y := rr.L.2 } :
        NonlinDASys.LinPoint n p m).Certifies
        sys U r q (fun s => x ((j : ℝ) * r + s)) (fun s => y ((j : ℝ) * r + s))
        (fun s => u ((j : ℝ) * r + s))) (fuel : ℕ) : -- --- STMT ---
    ∀ (k₀ N k : ℕ) (tk tf : ℝ) (Rk : Zonotope (Vec ℝ n))
      (L : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)) (Runion : Set (Vec ℝ n)),
      tk = (k : ℝ) * r → tf = (N : ℝ) * r → k ≤ N → k₀ + N ≤ K → 0 < N →
      x (((k₀ + k : ℕ) : ℝ) * r) ∈ Rk.construct →
      (0 < k → ∀ t ∈ Set.Icc 0 tf, t ≤ tk → x ((k₀ : ℝ) * r + t) ∈ Runion) →
      ∀ res, sys.reachLoop taylor corollary1 sub Lmax lam r (q + 2) U splitFn fuel tk tf Rk L
          Runion = some res → ∀ t ∈ Set.Icc 0 tf, x ((k₀ : ℝ) * r + t) ∈ res := by -- --- PROOF ---
  -- when the loop has run out of time, everything up to `t_f = t_k` is in the union
  have hterm : ∀ (k₀ N k : ℕ) (tk tf : ℝ) (Runion : Set (Vec ℝ n)), tk = (k : ℝ) * r →
      tf = (N : ℝ) * r → k ≤ N → 0 < N → ¬ tk < tf →
      (0 < k → ∀ t ∈ Set.Icc 0 tf, t ≤ tk → x ((k₀ : ℝ) * r + t) ∈ Runion) →
      ∀ t ∈ Set.Icc 0 tf, x ((k₀ : ℝ) * r + t) ∈ Runion := by
    intro k₀ N k tk tf Runion htk htf hkN hN hnot hcov t ht
    -- no time left means `k = N`, and then `hcov` covers everything
    have hNk : N ≤ k := by
      by_contra hlt
      exact hnot (by rw [htk, htf]; exact mul_lt_mul_of_pos_right (by exact_mod_cast
        (not_le.mp hlt)) hr)
    have hk : 0 < k := lt_of_lt_of_le hN hNk
    exact hcov hk t ht (ht.2.trans (by
      rw [htf, htk]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNk) hr.le))
  -- the induction on the fuel
  induction fuel with
  | zero =>
    intro k₀ N k tk tf Rk L Runion htk htf hkN hK hN hx hcov res hres
    simp only [NonlinDASys.reachLoop] at hres
    split at hres
    · simp at hres
    · next hnot =>
      obtain rfl := Option.some.inj hres
      exact hterm k₀ N k tk tf _ htk htf hkN hN hnot hcov
  | succ fuel ih =>
    -- one more pass of the loop
    intro k₀ N k tk tf Rk L Runion htk htf hkN hK hN hx hcov res hres
    simp only [NonlinDASys.reachLoop] at hres
    split at hres
    · next hlt =>
      have hkN' : k < N := by
        rw [htk, htf] at hlt
        exact_mod_cast (mul_lt_mul_iff_left₀ hr).mp hlt
      have hj : k₀ + k < K := by omega
      have hab : ((k₀ + k : ℕ) : ℝ) * r + r ≤ (K : ℝ) * r := by
        have h1 : ((k₀ + k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
        have := mul_le_mul_of_nonneg_right h1 hr.le
        push_cast at this ⊢
        linarith
      -- the run counted from `t_k`, started in `Rk`
      have run := traj.shift (a := ((k₀ + k : ℕ) : ℝ) * r) (b := r)
        (mul_nonneg (Nat.cast_nonneg _) hr.le) hab hx
      split at hres
      · simp at hres
      · next rr hrep =>
        obtain ⟨hRti, hexit⟩ := NonlinDASys.reachRepeat_spec sys (taylor Rk) corollary1 sub Lmax
          lam r (q + 2) Rk U (fuel + 1) L hrep
        have hcr := hcert (k₀ + k) hj (fuel + 1) Rk L rr hx hrep
        -- everything before `t_k` is already in the union, and `k > 0` if there is anything
        have hbefore : ∀ t ∈ Set.Icc 0 tf, t < tk → x ((k₀ : ℝ) * r + t) ∈ Runion := by
          intro t ht htlt
          have hpos : (0 : ℝ) < (k : ℝ) * r := htk ▸ lt_of_le_of_lt ht.1 htlt
          exact hcov (Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)) t ht htlt.le
        split at hres
        · next hsp =>
          -- lines 11-16: the errors are too large, the set is split and each half run again
          split at hres
          · next U1 U2 h1 h2 =>
            -- a time before `t_k` is in `Runion`, a later one in the half's run holding `x(t_k)`
            obtain rfl := Option.some.inj hres
            intro t ht
            by_cases htlt : t < tk
            · exact Or.inl (Or.inl (hbefore t ht htlt))
            · have hs : t - tk ∈ Set.Icc 0 (tf - tk) := ⟨by linarith, by linarith [ht.2]⟩
              have hrw : (k₀ : ℝ) * r + t = ((k₀ + k : ℕ) : ℝ) * r + (t - tk) := by
                rw [htk]; push_cast; ring
              have hNk : tf - tk = ((N - k : ℕ) : ℝ) * r := by
                rw [htf, htk, Nat.cast_sub hkN]; ring
              rw [hrw]
              rcases hsplit Rk hx with hx1 | hx2
              · exact Or.inl (Or.inr (ih (k₀ + k) (N - k) 0 0 (tf - tk) _ _ ∅ (by simp) hNk
                  (Nat.zero_le _) (by omega) (by omega) (by simpa using hx1)
                  (fun h => absurd h (lt_irrefl 0)) U1 h1 _ hs))
              · exact Or.inr (ih (k₀ + k) (N - k) 0 0 (tf - tk) _ _ ∅ (by simp) hNk
                  (Nat.zero_le _) (by omega) (by omega) (by simpa using hx2)
                  (fun h => absurd h (lt_irrefl 0)) U2 h2 _ hs)
          · simp at hres
        · next hsp =>
          -- lines 17-21: the exit was `L ⊆ L̄`, so the certificate at `L` holds at `L̄` too
          have hsub1 : sub rr.L.1 Lmax = true := by simpa using hsp
          have hLsub : sub rr.L.1 rr.Lbar.1 = true ∧ sub rr.L.2 rr.Lbar.2 = true := by
            simpa [hsub1, Bool.and_eq_true] using hexit
          have hcrb := NonlinDASys.LinPoint.certifies_of_subset (taylor Rk) sys U r q _ _ _
            (hsub _ _ hLsub.1) (hsub _ _ hLsub.2) hcr
          -- `linReach_outer` at `L`, for the state at `t_{k+1}`, and at `L̄`, for `Rᵈ(τ_k)`
          obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hcr
          obtain ⟨hnext, -⟩ := NonlinDASys.IsTrajectory.linReach_outer (Rinit := Rk) run hr hF hR hL
            hLa hus h0 hε
          obtain ⟨F', Rz', hF', hR', hL', hLa', hus', h0', hε'⟩ := hcrb
          obtain ⟨-, hint⟩ := NonlinDASys.IsTrajectory.linReach_outer (Rinit := Rk) run hr hF' hR'
            hL' hLa' hus' h0' hε'
          -- the loop from `t_{k+1}`, with `Rᵈ(τ_k)` joined to the union
          refine ih k₀ N (k + 1) (tk + r) tf _ rr.L (Runion ∪ rr.Rti.construct)
            (by rw [htk]; push_cast; ring) htf (by omega) hK hN ?_ ?_ res hres
          · have hrw : ((k₀ + (k + 1) : ℕ) : ℝ) * r = ((k₀ + k : ℕ) : ℝ) * r + r := by
              push_cast; ring
            rw [hrw]
            exact hnext
          · intro _ t ht htle
            by_cases htlt : t < tk
            · exact Or.inl (hbefore t ht htlt)
            · refine Or.inr ?_
              have hs : t - tk ∈ Set.Icc 0 r := ⟨by linarith, by linarith⟩
              have hrw : (k₀ : ℝ) * r + t = ((k₀ + k : ℕ) : ℝ) * r + (t - tk) := by
                rw [htk]; push_cast; ring
              rw [hrw, hRti]
              exact (hint (t - tk) hs).1
    · next hnot =>
      obtain rfl := Option.some.inj hres
      exact hterm k₀ N k tk tf _ htk htf hkN hN hnot hcov

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
