import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.hyperplaneOne`

`spectraShadow(sparse(1,n+1), c_one, [speye(n); sparse(1,n)])` of `convHull_`: the hyperplane
`ℝⁿ × {1}` of `ℝⁿ⁺¹`, the trivial inequality `0 ⪰ 0` with the last coordinate fixed to `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev SpectraShadow.hyperplaneOne (n : ℕ) : SpectraShadow (Vec ℝ (n + 1)) :=
  ⟨1, n, 0, fun _ => 0, Fin.append (0 : Vec ℝ n) (fun _ : Fin 1 => 1),
    fun j => Fin.append (Pi.single j 1 : Vec ℝ n) (0 : Vec ℝ 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
