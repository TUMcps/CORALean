module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.Global.Float.RatUp
public import CORALean.Global.Float.ToRat
public import CORALean.Global.LinProg.Simplex

@[expose] public section

/-!
# `HPolytope.emptyWeights`

Weights proposing a Farkas certificate that a polytope within the unit box is empty. The program
is the margin program `max t` over `A β + t ≤ b`, `Ae β + t ≤ be.sup`, `-Ae β + t ≤ -be.inf`,
`±βⱼ + t ≤ 1`: it is feasible and bounded, and its optimum is negative exactly when the polytope is
empty. Its dual is bounded too, the weights summing to one, which is what lets the simplex return
a certificate where the plain feasibility dual (unbounded for an empty polytope) returns nothing.
The weights are read back as `dualWeights` reads its own.

Nothing here is trusted: `ConZonotope.boundDotWeights` clamps every weight at zero and encloses the
residual it actually has, so a bad proposal costs the `true` only.

A NaN among the stored data reads through `ToRat` as `1.5 · 2 ^ 1024`, so the program solved
is another one. That costs tightness only: the checker sees the NaN in rounded arithmetic.
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

/-- The rows in ℚ, exactly, with the margin `t` as the last variable: `A`, `Ae`, `-Ae`, then the
unit box `I` and `-I`, each row ending in `1`. -/
def HPolytope.aux_marginRows (P : HPolytope 𝕋 (Vec 𝕋 h)) :
    Fin (P.m + (P.me + P.me) + (h + h)) → Fin (h + 1) → ℚ :=
  fun i j =>
    if hj : j.val < h then
      Fin.append
        (Fin.append (fun i j => ToRat.toRat (P.A i j))
          (Fin.append (fun i j => ToRat.toRat (P.Ae i j)) fun i j => -ToRat.toRat (P.Ae i j)))
        (Fin.append (fun i j => if i = j then 1 else 0) fun i j => if i = j then -1 else 0)
        i ⟨j.val, hj⟩
    else 1

/-- The right-hand sides matching `aux_marginRows`. -/
def HPolytope.aux_marginRhs (P : HPolytope 𝕋 (Vec 𝕋 h)) : Fin (P.m + (P.me + P.me) + (h + h)) → ℚ :=
  Fin.append
    (Fin.append (fun i => ToRat.toRat (P.b i))
      (Fin.append (fun i => ToRat.toRat (P.be.sup i)) fun i => -ToRat.toRat (P.be.inf i)))
    fun _ => 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Weights `(y, zu, zl)` for the rows `A`, `Ae ≤ be.sup` and `-Ae ≤ -be.inf`. All zero where the
simplex returns nothing. A proposal, not a certificate. -/
def HPolytope.emptyWeights (P : HPolytope 𝕋 (Vec 𝕋 h)) :
    Vec 𝕋 P.m × Vec 𝕋 P.me × Vec 𝕋 P.me :=
  let k := P.m + (P.me + P.me) + (h + h)
  -- maximise the margin `t`, the last variable
  let obj : Fin (h + 1) → ℚ := fun j => if j.val = h then 1 else 0
  match dualCandidate (64 * (k + h + 2)) (HPolytope.aux_marginRows P)
      (HPolytope.aux_marginRhs P) obj with
  | none => (fun _ => zero, fun _ => zero, fun _ => zero)
  | some w =>
    (fun i => ratUp (w (Fin.castAdd _ (Fin.castAdd _ i))),
     fun i => ratUp (w (Fin.castAdd _ (Fin.natAdd P.m (Fin.castAdd _ i)))),
     fun i => ratUp (w (Fin.castAdd _ (Fin.natAdd P.m (Fin.natAdd P.me i)))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
