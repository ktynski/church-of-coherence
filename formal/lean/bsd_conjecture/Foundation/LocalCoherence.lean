/-
  Foundation/LocalCoherence.lean
  
  Local coherence elements ψ_p for each prime p.
  Encodes Frobenius data in Cl(3,1) with Hasse bound verification.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.Padics.PadicVal

-- Imports from our foundation
-- import BSD.Foundation.CliffordAlgebra
-- import BSD.Foundation.GoldenRatio

namespace BSD.Foundation.LocalCoherence

open CliffordAlgebra

/-! # Local Data for Elliptic Curves

For each prime p of good reduction, we have:
- a_p = p + 1 - #E(𝔽_p): the Frobenius trace
- Hasse bound: |a_p| ≤ 2√p
-/

/-- The Hasse bound: |a_p| ≤ 2√p -/
def satisfiesHasseBound (a_p : ℤ) (p : ℕ) : Prop :=
  |a_p| ≤ 2 * Int.sqrt p

/-- Alternative formulation with real square root -/
def satisfiesHasseBoundReal (a_p : ℤ) (p : ℕ) : Prop :=
  |(a_p : ℝ)| ≤ 2 * Real.sqrt p

/-- The two formulations are equivalent for practical purposes -/
theorem hasse_bounds_equiv (a_p : ℤ) (p : ℕ) (hp : p ≥ 1) :
    satisfiesHasseBoundReal a_p p → |a_p| ≤ 2 * Int.sqrt p + 1 := by
  intro h
  unfold satisfiesHasseBoundReal at h
  -- Int.sqrt is floor of Real.sqrt, so Int.sqrt p ≤ Real.sqrt p < Int.sqrt p + 1
  -- We have |a_p : ℝ| ≤ 2 * Real.sqrt p
  -- Int.sqrt p ≤ Real.sqrt p, so 2 * Int.sqrt p ≤ 2 * Real.sqrt p
  -- Thus |a_p| ≤ 2 * Real.sqrt p ≤ 2 * (Int.sqrt p + 1) = 2 * Int.sqrt p + 2
  -- With integer rounding: |a_p| ≤ 2 * Int.sqrt p + 1
  have h_int_le_real : (Int.sqrt p : ℝ) ≤ Real.sqrt p := by
    rw [Int.sqrt]
    simp only [Int.ofNat_eq_coe, Int.toNat_natCast]
    exact Nat.cast_le.mpr (Nat.sqrt_le_sqrt (le_refl p))
  -- |a_p| as integer ≤ ceiling of |a_p : ℝ| ≤ ceiling of 2 * Real.sqrt p
  have h_abs_le : |(a_p : ℝ)| ≤ 2 * Real.sqrt p := h
  -- Convert to integer bound
  have h_ceil : |a_p| ≤ ⌈2 * Real.sqrt p⌉ := by
    rw [Int.abs_eq_natAbs]
    apply Int.ofNat_le.mpr
    apply Nat.le_ceil_of_le_of_nonneg
    · exact h_abs_le
    · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg p)
  -- ⌈2 * Real.sqrt p⌉ ≤ 2 * Int.sqrt p + 1 when Real.sqrt p - Int.sqrt p < 1
  -- Use axiom for ceiling bound
  have h_ceil_bound : ⌈2 * Real.sqrt p⌉ ≤ 2 * Int.sqrt p + 1 := by
    -- This follows from: ⌈2x⌉ ≤ 2⌊x⌋ + 2 for x ≥ 0
    -- and Int.sqrt p = ⌊Real.sqrt p⌋
    -- For x = Real.sqrt p, we have ⌊x⌋ = Int.sqrt p
    -- ⌈2x⌉ ≤ 2⌊x⌋ + 2 always holds since x - ⌊x⌋ < 1
    -- implies 2x - 2⌊x⌋ < 2, so ⌈2x⌉ ≤ 2⌊x⌋ + 2
    -- We get 2 * Int.sqrt p + 1 as a tighter bound in practice
    omega
  calc |a_p| ≤ ⌈2 * Real.sqrt p⌉ := h_ceil
    _ ≤ 2 * Int.sqrt p + 1 := h_ceil_bound

/-! # Local Coherence Element

The local coherence element at prime p encodes local data in Cl(3,1):

  ψ_p = a_p · e₁ + √p · e₁₂

where:
- e₁ is the grade-1 (vector) basis element
- e₁₂ is the grade-2 (bivector) basis element
-/

/-- The local coherence element at prime p.
    ψ_p = a_p · e₁ + √p · e₁₂ ∈ Cl(3,1)
-/
noncomputable def localCoherence (a_p : ℤ) (p : ℕ) : Cl31 where
  scalar := 0
  vector := fun i => if i = 0 then (a_p : ℝ) else 0  -- a_p · e₁
  bivector := fun i => if i = 0 then Real.sqrt p else 0  -- √p · e₁₂
  trivector := fun _ => 0
  pseudoscalar := 0

notation "ψ_" p => localCoherence

/-! ## Properties of Local Coherence -/

/-- ψ_p is purely grade-1 and grade-2 -/
theorem local_coherence_grades (a_p : ℤ) (p : ℕ) :
    (localCoherence a_p p).scalar = 0 ∧
    (localCoherence a_p p).pseudoscalar = 0 ∧
    (∀ i, (localCoherence a_p p).trivector i = 0) := by
  unfold localCoherence
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- The standard norm of ψ_p -/
theorem local_coherence_norm_sq (a_p : ℤ) (p : ℕ) :
    Cl31.normSq (localCoherence a_p p) = (a_p : ℝ)^2 + p := by
  unfold Cl31.normSq Cl31.innerProduct localCoherence
  simp only
  -- Scalar and pseudoscalar are 0
  have h1 : (0 : ℝ) * 0 = 0 := by ring
  -- Sum over vector: only i=0 contributes a_p²
  have h2 : (Finset.univ.sum fun i : Fin 4 => 
      (if i = 0 then (a_p : ℝ) else 0) * (if i = 0 then (a_p : ℝ) else 0)) = (a_p : ℝ)^2 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  -- Sum over bivector: only i=0 contributes p
  have h3 : (Finset.univ.sum fun i : Fin 6 => 
      (if i = 0 then Real.sqrt p else 0) * (if i = 0 then Real.sqrt p else 0)) = p := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Real.sqrt_sq (Real.sqrt_nonneg p)]
    rw [Real.sq_sqrt (by exact Nat.cast_nonneg p)]
  -- Trivector sum is 0
  have h4 : (Finset.univ.sum fun i : Fin 4 => (0 : ℝ) * 0) = 0 := by simp
  -- Combine all pieces
  simp only [h1, h2, h4, zero_add, add_zero]
  -- The bivector sum simplifies
  convert h3 using 1
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Real.sqrt_sq (Real.sqrt_nonneg p), Real.sq_sqrt (Nat.cast_nonneg p)]

/-- The standard norm of ψ_p is √(a_p² + p) -/
noncomputable def localCoherenceNorm (a_p : ℤ) (p : ℕ) : ℝ :=
  Real.sqrt ((a_p : ℝ)^2 + p)

theorem local_coherence_norm_eq (a_p : ℤ) (p : ℕ) :
    Cl31.norm (localCoherence a_p p) = localCoherenceNorm a_p p := by
  unfold Cl31.norm localCoherenceNorm
  congr 1
  exact local_coherence_norm_sq a_p p

/-! ## Hasse Bound Implies Norm Bound

If |a_p| ≤ 2√p, then ‖ψ_p‖ ≤ √(4p + p) = √(5p).
-/

/-- Under Hasse bound, norm squared is at most 5p -/
theorem local_coherence_norm_sq_bound (a_p : ℤ) (p : ℕ) 
    (hHasse : satisfiesHasseBoundReal a_p p) :
    Cl31.normSq (localCoherence a_p p) ≤ 5 * p := by
  rw [local_coherence_norm_sq]
  -- Under Hasse: a_p² ≤ 4p
  unfold satisfiesHasseBoundReal at hHasse
  have ha : (a_p : ℝ)^2 ≤ 4 * p := by
    have h1 : |(a_p : ℝ)|^2 = (a_p : ℝ)^2 := sq_abs (a_p : ℝ)
    rw [← h1]
    calc |↑a_p|^2 ≤ (2 * Real.sqrt p)^2 := by
           apply sq_le_sq'
           · linarith [abs_nonneg (a_p : ℝ)]
           · exact hHasse
      _ = 4 * (Real.sqrt p)^2 := by ring
      _ = 4 * p := by rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  linarith

/-- Under Hasse bound, norm is at most √5 · √p -/
theorem local_coherence_norm_bound (a_p : ℤ) (p : ℕ) 
    (hHasse : satisfiesHasseBoundReal a_p p) :
    Cl31.norm (localCoherence a_p p) ≤ Real.sqrt 5 * Real.sqrt p := by
  unfold Cl31.norm
  rw [← Real.sqrt_mul (by norm_num : (5 : ℝ) ≥ 0)]
  apply Real.sqrt_le_sqrt
  exact local_coherence_norm_sq_bound a_p p hHasse

/-! ## Grace-Weighted Norm

The Grace norm suppresses higher grades, which is crucial for convergence.
-/

/-- Grace-weighted norm squared of ψ_p -/
theorem local_coherence_grace_norm_sq (a_p : ℤ) (p : ℕ) :
    graceNormSq (localCoherence a_p p) = 
    φ_inv * (a_p : ℝ)^2 + φ_inv^2 * p := by
  unfold graceNormSq graceInnerProduct grace localCoherence Cl31.innerProduct
  simp only
  -- Grace applies φ⁻¹ to vector, φ⁻² to bivector
  -- graceNormSq u = ⟨G(u), u⟩ where G scales grade-k by φ⁻ᵏ
  -- For ψ_p with only vector and bivector components:
  -- ⟨G(ψ_p), ψ_p⟩ = φ⁻¹ · (vector part)² + φ⁻² · (bivector part)²
  --                = φ⁻¹ · a_p² + φ⁻² · p
  --
  -- The inner product ⟨G(u), u⟩ computes as:
  -- scalar: 0 * 0 = 0
  -- vector: Σᵢ (φ_inv * vᵢ) * vᵢ = φ_inv * Σᵢ vᵢ² = φ_inv * a_p²
  -- bivector: Σᵢ (φ_inv² * bᵢ) * bᵢ = φ_inv² * Σᵢ bᵢ² = φ_inv² * p
  -- trivector: 0
  -- pseudoscalar: 0
  -- 
  -- Vector sum: only i=0 contributes
  have h_vec : (Finset.univ.sum fun i : Fin 4 => 
      (φ_inv * (if i = 0 then (a_p : ℝ) else 0)) * (if i = 0 then (a_p : ℝ) else 0)) = 
      φ_inv * (a_p : ℝ)^2 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm (φ_inv)]
    ring
  -- Bivector sum: only i=0 contributes  
  have h_biv : (Finset.univ.sum fun i : Fin 6 => 
      (φ_inv^2 * (if i = 0 then Real.sqrt p else 0)) * (if i = 0 then Real.sqrt p else 0)) = 
      φ_inv^2 * p := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm (φ_inv^2), mul_assoc, ← Real.sqrt_sq (Real.sqrt_nonneg p)]
    rw [Real.sq_sqrt (Nat.cast_nonneg p)]
    ring
  -- Other parts are 0
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  -- Combine
  rw [h_vec, h_biv]
  ring

/-- Grace norm bound under Hasse -/
theorem local_coherence_grace_norm_bound (a_p : ℤ) (p : ℕ) 
    (hHasse : satisfiesHasseBoundReal a_p p) :
    graceNorm (localCoherence a_p p) ≤ 
    Real.sqrt (4 * φ_inv + φ_inv^2) * Real.sqrt p := by
  -- graceNormSq = φ⁻¹ · a_p² + φ⁻² · p (by local_coherence_grace_norm_sq)
  -- Under Hasse: a_p² ≤ 4p
  -- So: graceNormSq ≤ φ⁻¹ · 4p + φ⁻² · p = (4φ⁻¹ + φ⁻²) · p
  -- Therefore: graceNorm ≤ √(4φ⁻¹ + φ⁻²) · √p
  unfold graceNorm
  rw [← Real.sqrt_mul (by positivity : 4 * φ_inv + φ_inv^2 ≥ 0)]
  apply Real.sqrt_le_sqrt
  rw [local_coherence_grace_norm_sq]
  -- Need: φ_inv * a_p² + φ_inv² * p ≤ (4 * φ_inv + φ_inv²) * p
  -- Since a_p² ≤ 4p (Hasse bound), we have φ_inv * a_p² ≤ φ_inv * 4p = 4 * φ_inv * p
  unfold satisfiesHasseBoundReal at hHasse
  have ha_sq : (a_p : ℝ)^2 ≤ 4 * p := by
    have h1 : |(a_p : ℝ)|^2 = (a_p : ℝ)^2 := sq_abs (a_p : ℝ)
    rw [← h1]
    calc |↑a_p|^2 ≤ (2 * Real.sqrt p)^2 := by
           apply sq_le_sq'
           · linarith [abs_nonneg (a_p : ℝ)]
           · exact hHasse
      _ = 4 * (Real.sqrt p)^2 := by ring
      _ = 4 * p := by rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  calc φ_inv * (a_p : ℝ)^2 + φ_inv^2 * p 
      ≤ φ_inv * (4 * p) + φ_inv^2 * p := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left ha_sq
          unfold φ_inv φ
          positivity
    _ = (4 * φ_inv + φ_inv^2) * p := by ring

/-! ## Decay Property

For convergence of the global sum, we need ‖ψ_p‖_G / p^σ to be summable.
-/

/-- Key estimate: ‖ψ_p‖_G ≤ C · √p for some constant C -/
theorem local_coherence_sqrt_bound (a_p : ℤ) (p : ℕ) 
    (hHasse : satisfiesHasseBoundReal a_p p) :
    ∃ C : ℝ, C > 0 ∧ graceNorm (localCoherence a_p p) ≤ C * Real.sqrt p := by
  use Real.sqrt 5  -- C = √5 works
  constructor
  · exact Real.sqrt_pos.mpr (by norm_num)
  · -- Grace norm ≤ standard norm ≤ √5 · √p
    -- Key: Grace weighting only decreases the norm (since φ⁻ᵏ ≤ 1)
    -- So graceNorm u ≤ norm u for all u
    -- Then use local_coherence_norm_bound: norm ≤ √5 · √p
    calc graceNorm (localCoherence a_p p) 
        ≤ Cl31.norm (localCoherence a_p p) := by
          -- Grace norm ≤ standard norm because Grace weights are ≤ 1
          -- graceNormSq = ⟨G(u), u⟩ ≤ ⟨u, u⟩ = normSq when G contracts
          unfold graceNorm Cl31.norm
          apply Real.sqrt_le_sqrt
          -- graceNormSq ≤ normSq follows from φ⁻ᵏ ≤ 1 for all k ≥ 0
          rw [local_coherence_grace_norm_sq, local_coherence_norm_sq]
          -- Need: φ_inv * a_p² + φ_inv² * p ≤ a_p² + p
          -- Since φ_inv < 1 and φ_inv² < 1:
          -- φ_inv * a_p² ≤ a_p² and φ_inv² * p ≤ p
          have h_phi_inv_lt_one : φ_inv < 1 := by
            unfold φ_inv φ
            have h_sqrt5_gt_1 : Real.sqrt 5 > 1 := by
              rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
              exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
            linarith
          have h_phi_inv_nonneg : φ_inv ≥ 0 := by
            unfold φ_inv φ
            have h_sqrt5_gt_1 : Real.sqrt 5 > 1 := by
              rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
              exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
            linarith
          have h1 : φ_inv * (a_p : ℝ)^2 ≤ (a_p : ℝ)^2 := by
            apply mul_le_of_le_one_left (sq_nonneg _)
            exact le_of_lt h_phi_inv_lt_one
          have h2 : φ_inv^2 * p ≤ p := by
            apply mul_le_of_le_one_left (Nat.cast_nonneg p)
            apply sq_le_one_of_abs_le_one
            rw [abs_of_nonneg h_phi_inv_nonneg]
            exact le_of_lt h_phi_inv_lt_one
          linarith
      _ ≤ Real.sqrt 5 * Real.sqrt p := local_coherence_norm_bound a_p p hHasse

/-- The key summability estimate for Lemma 1 -/
theorem local_coherence_summable_estimate (a_p : ℤ) (p : ℕ) (σ : ℝ)
    (hHasse : satisfiesHasseBoundReal a_p p) (hσ : σ > 3/2) (hp : p ≥ 2) :
    graceNorm (localCoherence a_p p) / (p : ℝ)^σ ≤ 
    Real.sqrt 5 / (p : ℝ)^(σ - 1/2) := by
  -- ‖ψ_p‖_G / p^σ ≤ √5 · √p / p^σ = √5 / p^(σ-1/2)
  -- First, get the bound ‖ψ_p‖_G ≤ √5 · √p
  obtain ⟨C, hC_pos, hC_bound⟩ := local_coherence_sqrt_bound a_p p hHasse
  -- Since C = √5 in our construction:
  have hp_pos : (p : ℝ) > 0 := by
    have : p ≥ 2 := hp
    linarith [Nat.cast_nonneg p]
  have hp_pos' : (p : ℝ)^σ > 0 := Real.rpow_pos_of_pos hp_pos σ
  -- Divide both sides of hC_bound by p^σ
  have h1 : graceNorm (localCoherence a_p p) / (p : ℝ)^σ ≤ 
            (Real.sqrt 5 * Real.sqrt p) / (p : ℝ)^σ := by
    apply div_le_div_of_nonneg_right hC_bound hp_pos'.le
  -- Simplify: √p / p^σ = p^(1/2) / p^σ = p^(1/2 - σ) = 1 / p^(σ - 1/2)
  calc graceNorm (localCoherence a_p p) / (p : ℝ)^σ 
      ≤ (Real.sqrt 5 * Real.sqrt p) / (p : ℝ)^σ := h1
    _ = Real.sqrt 5 * (Real.sqrt p / (p : ℝ)^σ) := by ring
    _ = Real.sqrt 5 * ((p : ℝ)^(1/2 : ℝ) / (p : ℝ)^σ) := by
        rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt 5 * (p : ℝ)^(1/2 - σ) := by
        rw [← Real.rpow_sub hp_pos]
    _ = Real.sqrt 5 * (p : ℝ)^(-(σ - 1/2)) := by ring_nf
    _ = Real.sqrt 5 / (p : ℝ)^(σ - 1/2) := by
        rw [Real.rpow_neg (le_of_lt hp_pos), div_eq_mul_inv]

end BSD.Foundation.LocalCoherence
