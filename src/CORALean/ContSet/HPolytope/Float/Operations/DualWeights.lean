import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.Global.Float.RatUp
import CORALean.Global.Float.ToRat
import CORALean.Global.LinProg.Simplex

/-!
# `HPolytope.dualWeights`

The float layer's linear-program driver, and deliberately part of no proof. It
reads the stored rows back into ℚ through `ToRat`, so the simplex sees exactly
the program the floats denote, solves its dual there with `dualCandidate`, and
rounds the weights into `𝕋` with `ratUp`.

The program is `max dᵀβ` over the polytope within the unit box `|βⱼ| ≤ 1`, a constrained
zonotope's coefficient domain. The box rows keep it bounded, so the dual is feasible; their
weights are then dropped, the checker paying for the box by the residual against `Σ |rⱼ|`. An
interval equality row is two inequalities, `Ae β ≤ be.sup` and `-Ae β ≤ -be.inf`, a weight each.

Nothing here is trusted: a negative, badly rounded or missing (`none`, the pivot
budget ran out) weight costs tightness only, because the checker clamps every
weight at zero and encloses the residual it actually has, in rounded arithmetic.

A NaN in the stored data reads through `ToRat` as `1.5 · 2 ^ 1024`: another program, which
costs tightness only, the checker seeing the NaN in rounded arithmetic.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The rows in ℚ, exactly: `A`, `Ae`, `-Ae`, then the unit box `I` and `-I`. -/
def HPolytope.aux_boxRows (P : HPolytope 𝕋 (Vec 𝕋 h)) :
    Fin (P.m + (P.me + P.me) + (h + h)) → Fin h → ℚ :=
  Fin.append
    (Fin.append (fun i j => ToRat.toRat (P.A i j))
      (Fin.append (fun i j => ToRat.toRat (P.Ae i j)) fun i j => -ToRat.toRat (P.Ae i j)))
    (Fin.append (fun i j => if i = j then 1 else 0) fun i j => if i = j then -1 else 0)

/-- The right-hand sides matching `aux_boxRows`. -/
def HPolytope.aux_boxRhs (P : HPolytope 𝕋 (Vec 𝕋 h)) : Fin (P.m + (P.me + P.me) + (h + h)) → ℚ :=
  Fin.append
    (Fin.append (fun i => ToRat.toRat (P.b i))
      (Fin.append (fun i => ToRat.toRat (P.be.sup i)) fun i => -ToRat.toRat (P.be.inf i)))
    fun _ => 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Weights `(y, zu, zl)` for the rows `A`, `Ae ≤ be.sup` and `-Ae ≤ -be.inf`,
proposed for the direction `d` over the polytope within the unit box. All zero
where the simplex returns nothing. A proposal, not a certificate. -/
def HPolytope.dualWeights (P : HPolytope 𝕋 (Vec 𝕋 h)) (d : Fin h → ℚ) :
    Vec 𝕋 P.m × Vec 𝕋 P.me × Vec 𝕋 P.me :=
  let k := P.m + (P.me + P.me) + (h + h)
  match dualCandidate (64 * (k + h + 1)) (HPolytope.aux_boxRows P) (HPolytope.aux_boxRhs P) d with
  | none => (fun _ => zero, fun _ => zero, fun _ => zero)
  | some w =>
    (fun i => ratUp (w (Fin.castAdd _ (Fin.castAdd _ i))),
     fun i => ratUp (w (Fin.castAdd _ (Fin.natAdd P.m (Fin.castAdd _ i)))),
     fun i => ratUp (w (Fin.castAdd _ (Fin.natAdd P.m (Fin.natAdd P.me i)))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
