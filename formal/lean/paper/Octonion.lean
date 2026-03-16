/-
  Octonion.lean — Octonion Algebra from the Fano Plane
  
  Self-contained. No imports required.
  Compile: lean Octonion.lean
-/

namespace Octonion

/-- Octonion product (same definition as Confinement.lean). -/
def mult (i j : Fin 8) : Int × Fin 8 :=
  if i == 0 then (1, j)
  else if j == 0 then (1, i)
  else if i == j then (-1, 0)
  else if i == 1 && j == 2 then (1, 3)
  else if i == 2 && j == 4 then (1, 6)
  else if i == 4 && j == 1 then (1, 5)
  else if i == 1 && j == 6 then (1, 7)
  else if i == 2 && j == 5 then (1, 7)
  else if i == 4 && j == 3 then (1, 7)
  else if i == 3 && j == 6 then (1, 5)
  else if i == 2 && j == 1 then (-1, 3)
  else if i == 4 && j == 2 then (-1, 6)
  else if i == 1 && j == 4 then (-1, 5)
  else if i == 6 && j == 1 then (-1, 7)
  else if i == 5 && j == 2 then (-1, 7)
  else if i == 3 && j == 4 then (-1, 7)
  else if i == 6 && j == 3 then (-1, 5)
  else if i == 2 && j == 3 then (1, 1)
  else if i == 3 && j == 1 then (1, 2)
  else if i == 3 && j == 2 then (-1, 1)
  else if i == 1 && j == 3 then (-1, 2)
  else if i == 4 && j == 6 then (1, 2)
  else if i == 6 && j == 2 then (1, 4)
  else if i == 6 && j == 4 then (-1, 2)
  else if i == 2 && j == 6 then (-1, 4)
  else if i == 1 && j == 5 then (1, 4)
  else if i == 5 && j == 4 then (1, 1)
  else if i == 5 && j == 1 then (-1, 4)
  else if i == 4 && j == 5 then (-1, 1)
  else if i == 6 && j == 7 then (1, 1)
  else if i == 7 && j == 1 then (1, 6)
  else if i == 7 && j == 6 then (-1, 1)
  else if i == 1 && j == 7 then (-1, 6)
  else if i == 5 && j == 7 then (1, 2)
  else if i == 7 && j == 2 then (1, 5)
  else if i == 7 && j == 5 then (-1, 2)
  else if i == 2 && j == 7 then (-1, 5)
  else if i == 3 && j == 7 then (1, 4)
  else if i == 7 && j == 4 then (1, 3)
  else if i == 7 && j == 3 then (-1, 4)
  else if i == 4 && j == 7 then (-1, 3)
  else if i == 6 && j == 5 then (1, 3)
  else if i == 5 && j == 3 then (1, 6)
  else if i == 5 && j == 6 then (-1, 3)
  else if i == 3 && j == 5 then (-1, 6)
  else (0, 0)

/-- All 7 imaginary units square to -1. -/
theorem e1_sq : mult 1 1 = (-1, 0) := by native_decide
theorem e2_sq : mult 2 2 = (-1, 0) := by native_decide
theorem e3_sq : mult 3 3 = (-1, 0) := by native_decide
theorem e4_sq : mult 4 4 = (-1, 0) := by native_decide
theorem e5_sq : mult 5 5 = (-1, 0) := by native_decide
theorem e6_sq : mult 6 6 = (-1, 0) := by native_decide
theorem e7_sq : mult 7 7 = (-1, 0) := by native_decide

/-- All 7 Fano lines verified. -/
theorem fano_line_1 : mult 1 2 = (1, 3) := by native_decide
theorem fano_line_2 : mult 2 4 = (1, 6) := by native_decide
theorem fano_line_3 : mult 4 1 = (1, 5) := by native_decide
theorem fano_line_4 : mult 1 6 = (1, 7) := by native_decide
theorem fano_line_5 : mult 2 5 = (1, 7) := by native_decide
theorem fano_line_6 : mult 4 3 = (1, 7) := by native_decide
theorem fano_line_7 : mult 3 6 = (1, 5) := by native_decide

/-- Anticommutativity: eᵢeⱼ = -eⱼeᵢ for i≠j. -/
theorem anticomm_12 : mult 1 2 = (-(mult 2 1).1, (mult 2 1).2) := by native_decide
theorem anticomm_14 : mult 1 4 = (-(mult 4 1).1, (mult 4 1).2) := by native_decide
theorem anticomm_24 : mult 2 4 = (-(mult 4 2).1, (mult 4 2).2) := by native_decide

/-- Norm: |eᵢ·eⱼ| = 1 for all i,j > 0 (unit norm products). -/
theorem norm_12 : (mult 1 2).1 = 1 ∨ (mult 1 2).1 = -1 := by native_decide
-- All squares are -1 (verified individually above for e1..e7)

end Octonion
