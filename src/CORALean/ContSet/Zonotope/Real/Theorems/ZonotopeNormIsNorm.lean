module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm

@[expose] public section

/-!
# The zonotope norm is a norm

`[1, Thm. 1]`: for a generator matrix of full rank `n`, `ν` is a norm on `ℝⁿ`. Full rank is
read as the generator map being onto (`[1, Lemma 2]`), which makes every point reachable,
so `coeffNorm`'s triangle inequality, homogeneity and definiteness hold everywhere: the
constraints on the minimizer are linear and `‖·‖∞` is a norm, as the printed proof says.
Over any real module.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_isNorm (Z : Zonotope α) (hG : Function.Surjective Z.genMap) :
    (∀ x y, Z.zonotopeNorm (x + y) ≤ Z.zonotopeNorm x + Z.zonotopeNorm y) ∧
      (∀ (a : ℝ) x, Z.zonotopeNorm (a • x) = |a| * Z.zonotopeNorm x) ∧
      ∀ x, Z.zonotopeNorm x = 0 ↔ x = 0 :=
  ⟨fun x y => coeffNorm_add_le _ (hG x) (hG y), fun a x => coeffNorm_smul _ (hG x) a,
    fun x => coeffNorm_eq_zero_iff _ (hG x)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
