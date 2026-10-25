module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachRepeat

@[expose] public section

/-!
# [1, Alg. 1]'s time loop and its splits

Lines 2-23 of `[1, Alg. 1]`: while `t_k < t_f`, linearize at the current set (line 3, `taylor`),
run the error loop of lines 4-10 (`reachRepeat`), and either split the set when the errors exceed
`L_max` (lines 11-16: each half is run on the remaining horizon `t_f - t_k` by this same loop) or
step to `t_{k+1}` (lines 17-21: `Rᵈ(t_{k+1})` from the computed `L`, and `Rᵈ(τ_k)` of line 7,
joined to `R_union`). The split `splitFn` and the linearization `taylor` are arguments: CORA picks
the generator to split by a heuristic, and the expansion point `z*`, with `u* = center(U)`, is
`taylor`'s. `fuel` bounds the iterations and splits along any one path, the result being `none`
where it runs out; the union is a `Set`. `L_max` and `L ⊆ L̄` are read through `sub`.

## Inputs
* `sys` – system
* `taylor` – linearization of a start set
* `corollary1` – error-set computation
* `sub` – subset test
* `Lmax` – bound on the linearization errors
* `lam` – enlargement factor
* `r` – step size
* `η` – Taylor order
* `U` – input zonotope
* `splitFn` – set splitting

## Output
* the union of everything covered, or none

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


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
      -- 2. `while t_k < t_f`
      if tk < tf then
        -- 3. `taylor ← ` the linearization point of `R_k`
        let T := taylor Rk
        -- 4.-10. `repeat … until L ⊆ L̄`
        match NonlinDASys.reachRepeat sys T corollary1 sub Lmax lam r η Rk U (fuel + 1) L with
        | none => none
        | some rr =>
          -- 11. `if L ⊄ L_max`
          if !sub rr.L.1 Lmax then
            -- 12. split `R_k` into two sets
            let Rsplit := splitFn Rk
            -- 13.-14. `L ← {0}`, and Alg. 1 on each half over `[0, t_f - t_k]`
            let L0 := (Zonotope.ofPoint (0 : Vec ℝ n), Zonotope.ofPoint (0 : Vec ℝ p))
            match NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
                0 (tf - tk) Rsplit.1 L0 ∅,
              NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
                0 (tf - tk) Rsplit.2 L0 ∅ with
            -- 15.-16. `R_union ← R_union ∪ …` of both halves
            | some U1, some U2 => some (Runion ∪ U1 ∪ U2)
            | _, _ => none
          else
            -- 18.-19. `R(τ_k), R_{k+1}` by `linReach` at the errors `L`
            let R := NonlinDASys.linReach (sys.f T.xs T.ys T.us) (sys.g T.xs T.ys T.us)
              T.A T.B T.C T.D T.E T.F_inv T.xs T.ys T.us Rk U rr.L.1 rr.L.2 r η
            -- 20.-21. `t_k ← t_k + r`, `R_union ← R_union ∪ R(τ_k)`
            NonlinDASys.reachLoop sys taylor corollary1 sub Lmax lam r η U splitFn fuel
              (tk + r) tf R.1 rr.L (Runion ∪ rr.Rti.construct)
      else some Runion

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
