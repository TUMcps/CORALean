module

public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapIntEq
public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `quadint` encloses the quadratic map at every matrix of the interval

[1, Prop. 3]: if each `H⁽ⁱ⁾` lies in the interval matrix `Hc⁽ⁱ⁾ ⊕ [-HΔ⁽ⁱ⁾, HΔ⁽ⁱ⁾]`, then
`{φ | φᵢ = zᵀH⁽ⁱ⁾z, z ∈ Z} ⊆ quadint(H, Z)`. The factor `½` the proposition carries on both sides
is dropped, and its first inclusion is [1, Eq. 23]; this is the second. Each coordinate may take
its own matrix of the interval. The printed proof bounds the interval center and generators by
the subdistributivity of [1, Eq. 22]. Here the route is [1, Thm. 1]: `zᵀH⁽ⁱ⁾z = zᵀHc⁽ⁱ⁾z +
zᵀ(H⁽ⁱ⁾ - Hc⁽ⁱ⁾)z`, the first in `quad(Hc, Z)` by [1, Lemma 1], the second at most
`|z|ᵀHΔ⁽ⁱ⁾|z| ≤ |Z|ᵀHΔ⁽ⁱ⁾|Z|` in absolute value, so in the box `[-η, η]`.

## Inputs
* `Hc` – center quadratic matrices
* `HΔ` – radius quadratic matrices
* `Z` – zonotope
* `H` – actual quadratic matrices
* `z` – point of the zonotope

## Hypotheses
* `hH` – matrices within the radius of the center
* `hz` – `z` lies in `Z`

## Conclusion
* the quadratic image lies in the result

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An entrywise bound `S` on `E` bounds the quadratic form at anything `a` covers. -/
theorem Zonotope.aux_quadMapInt_abs_quad_le {E S : Mat ℝ n n} {x a : Vec ℝ n}
    (hE : ∀ j k, |E j k| ≤ S j k) (hx : ∀ j, |x j| ≤ a j) :
    |x ⬝ᵥ (E *ᵥ x)| ≤ a ⬝ᵥ (S *ᵥ a) := by -- --- PROOF ---
  have ha : ∀ j, 0 ≤ a j := fun j => (abs_nonneg _).trans (hx j)
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  -- three factors, each replaced by what bounds it
  rw [abs_mul, abs_mul]
  calc |x j| * (|E j k| * |x k|) ≤ a j * (S j k * a k) :=
        mul_le_mul (hx j) (mul_le_mul (hE j k) (hx k) (abs_nonneg _)
          ((abs_nonneg _).trans (hE j k))) (by positivity) (ha j)
    _ = a j * (S j k * a k) := rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `{φ | φᵢ = zᵀH⁽ⁱ⁾z, z ∈ Z}` at every `H⁽ⁱ⁾ ∈ Hc⁽ⁱ⁾ ⊕ [-HΔ⁽ⁱ⁾, HΔ⁽ⁱ⁾]` lies in
`quadint(H, Z)`. -/
theorem Zonotope.quadMapInt_outer (Hc HΔ : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n))
    {H : Fin m → Mat ℝ n n} (hH : ∀ i j k, |H i j k - Hc i j k| ≤ HΔ i j k)
    {z : Vec ℝ n} (hz : z ∈ Z.construct) :
    (fun i => z ⬝ᵥ (H i *ᵥ z)) ∈ (Z.quadMapInt Hc HΔ).construct := by -- --- PROOF ---
  rw [Zonotope.quadMapInt_eq, ← Zonotope.plus_exact]
  -- the midpoint part, in `quad(Hc, Z)` by [1, Lemma 1]
  refine ⟨fun i => z ⬝ᵥ (Hc i *ᵥ z), Zonotope.quadMap_outer Hc Z ⟨z, hz, rfl⟩,
    fun i => z ⬝ᵥ ((H i - Hc i) *ᵥ z), Interval.zonotope_contains _ ?_, ?_⟩
  -- the rest, at most `|Z|ᵀHΔ⁽ⁱ⁾|Z|` in absolute value
  · obtain ⟨β, hβ, hzβ⟩ := Zonotope.mem_construct_iff.mp hz
    intro i
    have hb := Zonotope.aux_quadMapInt_abs_quad_le (E := H i - Hc i) (S := HΔ i)
      (fun j k => by simpa using hH i j k) (Zonotope.abs_le_absBound hβ hzβ)
    exact abs_le.mp hb
  · funext i
    simp [Matrix.sub_mulVec, dotProduct_sub]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
