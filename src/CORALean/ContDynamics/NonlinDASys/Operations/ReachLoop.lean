import CORALean.ContDynamics.NonlinDASys.Operations.ReachRepeat

/-!
# [1, Alg. 1]'s time loop and its splits

Lines 2-23 of `[1, Alg. 1]`: while `t_k < t_f`, linearize at the current set (line 3, `taylor`),
run the error loop of lines 4-10 (`reachRepeat`), and either split the set when the errors
exceed `L_max` (lines 11-16: each half is run on the remaining horizon `t_f - t_k` by this same
loop from `t_0 = 0`, `L = {0}`, `R_union = ∅`, the recursion `reach(R^(j)(t_k), t_f - t_k, ...)`
of lines 13-14) or step to `t_{k+1}` (lines 17-21: `Rᵈ(t_{k+1})` from the computed `L`, and
`Rᵈ(τ_k)` of line 7, not recomputed at `L`, joined to `R_union`). The split `splitFn` and the
linearization `taylor` are arguments: CORA picks the generator to split by a heuristic, and
the expansion point `z*`, with `u* = center(U)`, is `taylor`'s. `fuel` bounds the iterations
and splits along any one path, the result being `none` where it runs out; the union is a `Set`,
being no zonotope. `L_max` and `L ⊆ L̄` are read through `sub`.

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

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] lines 2-23 from the time `tk`, start set `Rk`, errors `L` and union `Runion` so
far, with horizon `tf`: the union of everything covered, or `none` where `fuel` runs out. -/
noncomputable def NonlinDASys.reachLoop (sys : NonlinDASys n p m)
    (taylor : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (Lmax : Zonotope (Vec ℝ n)) (lam r : ℝ) (η : ℕ) (U : Zonotope (Vec ℝ m))
    (splitFn : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) :
    ℕ → ℝ → ℝ → Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p) →
      Set (Vec ℝ n) → Option (Set (Vec ℝ n))
  | 0, tk, tf, _, _, Runion => if tk < tf then none else some Runion
  | fuel + 1, tk, tf, Rk, L, Runion =>
      if tk < tf then                                                        -- l. 2
        let T := taylor Rk                                                   -- l. 3
        match NonlinDASys.reachRepeat sys T corollary1 sub Lmax lam r η Rk U (fuel + 1) L with
        | none => none                                                       -- l. 4-10
        | some rr =>
          if !sub rr.L.1 Lmax then                                           -- l. 11
            let Rsplit := splitFn Rk                                         -- l. 12
            let L0 := (Zonotope.ofPoint (0 : Vec ℝ n), Zonotope.ofPoint (0 : Vec ℝ p))  -- L = {0}
            match NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
                0 (tf - tk) Rsplit.1 L0 ∅,                                   -- l. 13
              NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
                0 (tf - tk) Rsplit.2 L0 ∅ with                               -- l. 14
            | some U1, some U2 => some (Runion ∪ U1 ∪ U2)                    -- l. 15-16
            | _, _ => none
          else
            let R := NonlinDASys.linReach (sys.f T.xs T.ys T.us) (sys.g T.xs T.ys T.us)
              T.A T.B T.C T.D T.E T.F_inv T.xs T.ys T.us Rk U rr.L.1 rr.L.2 r η   -- l. 18-19
            NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
              (tk + r) tf R.1 rr.L (Runion ∪ rr.Rti.construct)               -- l. 20-21
      else some Runion

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
