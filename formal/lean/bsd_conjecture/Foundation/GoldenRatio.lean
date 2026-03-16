/-
  Foundation/GoldenRatio.lean
  
  Rigorous proofs of golden ratio properties needed for FSCTF-BSD.
  The golden ratio φ = (1 + √5)/2 is fundamental to the Grace operator.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace BSD.Foundation.GoldenRatio

/-! # The Golden Ratio

φ = (1 + √5)/2 ≈ 1.618033988749895

The unique positive root of x² = x + 1.
-/

/-- The golden ratio φ = (1 + √5)/2 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- Alternative notation -/
noncomputable abbrev phi : ℝ := φ

/-! ## Basic Properties -/

/-- √5 is positive -/
lemma sqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)

/-- √5 squared equals 5 -/
lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)

/-- φ is positive -/
theorem phi_pos : φ > 0 := by
  unfold φ
  have h1 : Real.sqrt 5 > 0 := sqrt5_pos
  have h2 : (1 : ℝ) + Real.sqrt 5 > 0 := by linarith
  exact div_pos h2 (by norm_num : (2 : ℝ) > 0)

/-- φ ≠ 0 -/
theorem phi_ne_zero : φ ≠ 0 := ne_of_gt phi_pos

/-- φ > 1 -/
theorem phi_gt_one : φ > 1 := by
  unfold φ
  have h : Real.sqrt 5 > 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
  linarith

/-! ## The Fundamental Identity: φ² = φ + 1 -/

/-- THE CORE THEOREM: φ² = φ + 1 -/
theorem phi_squared : φ ^ 2 = φ + 1 := by
  unfold φ
  have h5 : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  field_simp
  ring_nf
  rw [h5]
  ring

/-- Alternative form: φ² - φ - 1 = 0 -/
theorem phi_char_eq : φ ^ 2 - φ - 1 = 0 := by
  rw [phi_squared]
  ring

/-- φ is a root of x² - x - 1 -/
theorem phi_is_root : φ ^ 2 - φ - 1 = 0 := phi_char_eq

/-! ## The Inverse: φ⁻¹ = φ - 1 -/

/-- The inverse of φ equals φ - 1 -/
theorem phi_inv : φ⁻¹ = φ - 1 := by
  have h := phi_squared
  have hne : φ ≠ 0 := phi_ne_zero
  -- From φ² = φ + 1, divide by φ to get φ = 1 + 1/φ
  -- So 1/φ = φ - 1
  field_simp [hne] at h ⊢
  linarith

/-- φ⁻¹ ≈ 0.618... (is positive) -/
theorem phi_inv_pos : φ⁻¹ > 0 := by
  rw [phi_inv]
  have h := phi_gt_one
  linarith

/-- φ⁻¹ < 1 -/
theorem phi_inv_lt_one : φ⁻¹ < 1 := by
  rw [phi_inv]
  have h := phi_squared
  -- φ - 1 < 1 iff φ < 2
  suffices φ < 2 by linarith
  unfold φ
  have hsq : Real.sqrt 5 < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) < 9)
  linarith

/-! ## Powers of φ -/

/-- Fibonacci-like recurrence: φⁿ⁺² = φⁿ⁺¹ + φⁿ -/
theorem phi_fib_recurrence (n : ℕ) : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
  have h := phi_squared
  calc φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
    _ = φ ^ n * (φ + 1) := by rw [h]
    _ = φ ^ n * φ + φ ^ n := by ring
    _ = φ ^ (n + 1) + φ ^ n := by ring

/-- φ³ = φ² + φ = 2φ + 1 -/
theorem phi_cubed : φ ^ 3 = 2 * φ + 1 := by
  calc φ ^ 3 = φ ^ 2 * φ := by ring
    _ = (φ + 1) * φ := by rw [phi_squared]
    _ = φ ^ 2 + φ := by ring
    _ = (φ + 1) + φ := by rw [phi_squared]
    _ = 2 * φ + 1 := by ring

/-- φ⁴ = φ³ + φ² = 3φ + 2 -/
theorem phi_fourth : φ ^ 4 = 3 * φ + 2 := by
  calc φ ^ 4 = φ ^ 3 * φ := by ring
    _ = (2 * φ + 1) * φ := by rw [phi_cubed]
    _ = 2 * φ ^ 2 + φ := by ring
    _ = 2 * (φ + 1) + φ := by rw [phi_squared]
    _ = 3 * φ + 2 := by ring

/-! ## Negative Powers (for Grace operator) -/

/-- φ⁻² = φ⁻¹ - 1 + 1 = 2 - φ -/
theorem phi_inv_squared : φ⁻¹ ^ 2 = 2 - φ := by
  rw [phi_inv]
  have h := phi_squared
  calc (φ - 1) ^ 2 = φ ^ 2 - 2 * φ + 1 := by ring
    _ = (φ + 1) - 2 * φ + 1 := by rw [h]
    _ = 2 - φ := by ring

/-- φ⁻² > 0 -/
theorem phi_inv_sq_pos : φ⁻¹ ^ 2 > 0 := by
  rw [phi_inv_squared]
  have h := phi_gt_one
  -- Need 2 - φ > 0, i.e., φ < 2
  suffices φ < 2 by linarith
  unfold φ
  have hsq : Real.sqrt 5 < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) < 9)
  linarith

/-- φ⁻³ = (φ - 1)³ = ... -/
theorem phi_inv_cubed : φ⁻¹ ^ 3 = 2 * φ - 3 := by
  rw [phi_inv]
  have h := phi_squared
  calc (φ - 1) ^ 3 = φ ^ 3 - 3 * φ ^ 2 + 3 * φ - 1 := by ring
    _ = (2 * φ + 1) - 3 * (φ + 1) + 3 * φ - 1 := by rw [phi_cubed, phi_squared]
    _ = 2 * φ - 3 := by ring

/-- φ⁻⁴ for Grace operator -/
theorem phi_inv_fourth : φ⁻¹ ^ 4 = 5 - 3 * φ := by
  rw [phi_inv]
  have h := phi_squared
  calc (φ - 1) ^ 4 = φ ^ 4 - 4 * φ ^ 3 + 6 * φ ^ 2 - 4 * φ + 1 := by ring
    _ = (3 * φ + 2) - 4 * (2 * φ + 1) + 6 * (φ + 1) - 4 * φ + 1 := by 
        rw [phi_fourth, phi_cubed, phi_squared]
    _ = 5 - 3 * φ := by ring

/-! ## Bounds for Grace Coefficients -/

/-- All Grace coefficients are positive -/
theorem phi_inv_pow_pos (k : ℕ) : φ⁻¹ ^ k > 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h := phi_inv_pos
    calc φ⁻¹ ^ (n + 1) = φ⁻¹ ^ n * φ⁻¹ := by ring
      _ > 0 := mul_pos ih h

/-- Grace coefficients decay: φ⁻ᵏ < φ⁻⁽ᵏ⁻¹⁾ for k ≥ 1 -/
theorem phi_inv_pow_decreasing (k : ℕ) (hk : k ≥ 1) : 
    φ⁻¹ ^ k < φ⁻¹ ^ (k - 1) := by
  have h1 : φ⁻¹ < 1 := phi_inv_lt_one
  have h2 : φ⁻¹ > 0 := phi_inv_pos
  cases k with
  | zero => omega
  | succ n =>
    simp only [add_tsub_cancel_right]
    calc φ⁻¹ ^ (n + 1) = φ⁻¹ ^ n * φ⁻¹ := by ring
      _ < φ⁻¹ ^ n * 1 := by {
        apply mul_lt_mul_of_pos_left h1
        exact phi_inv_pow_pos n
      }
      _ = φ⁻¹ ^ n := by ring

/-- Upper bound: φ⁻ᵏ ≤ 1 for all k -/
theorem phi_inv_pow_le_one (k : ℕ) : φ⁻¹ ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h := phi_inv_lt_one
    calc φ⁻¹ ^ (n + 1) = φ⁻¹ ^ n * φ⁻¹ := by ring
      _ ≤ 1 * φ⁻¹ := by {
        apply mul_le_mul_of_nonneg_right ih
        exact le_of_lt phi_inv_pos
      }
      _ = φ⁻¹ := by ring
      _ < 1 := h
      _ ≤ 1 := le_refl 1

/-- Lower bound: φ⁻ᵏ ≥ φ⁻⁴ for k ≤ 4 -/
theorem phi_inv_pow_lower_bound (k : ℕ) (hk : k ≤ 4) : 
    φ⁻¹ ^ k ≥ φ⁻¹ ^ 4 := by
  -- Since φ⁻¹ < 1, higher powers are smaller
  have h1 : φ⁻¹ < 1 := phi_inv_lt_one
  have h2 : φ⁻¹ > 0 := phi_inv_pos
  -- φ⁻ᵏ ≥ φ⁻⁴ when k ≤ 4
  apply pow_le_pow_right_of_le_one (le_of_lt h2) (le_of_lt h1) hk

/-! ## Numerical Approximations (for verification) -/

/-- φ is between 1.6 and 1.7 -/
theorem phi_bounds : 1.6 < φ ∧ φ < 1.7 := by
  constructor
  · -- Lower bound: 1.6 < φ
    unfold φ
    have h : Real.sqrt 5 > 2.2 := by
      rw [← Real.sqrt_sq (by norm_num : (2.2 : ℝ) ≥ 0)]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    linarith
  · -- Upper bound: φ < 1.7
    unfold φ
    have h : Real.sqrt 5 < 2.4 := by
      rw [← Real.sqrt_sq (by norm_num : (2.4 : ℝ) ≥ 0)]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    linarith

/-- φ⁻¹ is between 0.6 and 0.7 -/
theorem phi_inv_bounds : 0.6 < φ⁻¹ ∧ φ⁻¹ < 0.7 := by
  rw [phi_inv]
  constructor
  · -- 0.6 < φ - 1 iff 1.6 < φ
    have ⟨h, _⟩ := phi_bounds
    linarith
  · -- φ - 1 < 0.7 iff φ < 1.7
    have ⟨_, h⟩ := phi_bounds
    linarith

end BSD.Foundation.GoldenRatio
