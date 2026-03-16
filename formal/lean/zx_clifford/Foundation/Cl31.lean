/-
  Foundation/Cl31.lean

  Clifford Algebra Cl(3,1) using Mathlib's CliffordAlgebra

  This defines the proper mathematical foundation for ZX-calculus semantics
  using Mathlib's formalized Clifford algebra infrastructure.

  AXIOM STATUS: 0 axioms (all 4 original axioms eliminated)
    - minkowskiQ: constructed via QuadraticForm.ofPolar
    - minkowskiQ_eval: proved from construction
    - rotor_mul_generic: proved via distributivity + trig addition
    - hadamard_sq: proved from orthogonality + squared norms
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ZXClifford.Foundation

open CliffordAlgebra

/-! ## The Minkowski Quadratic Form -/

abbrev V4 := Fin 4 → ℝ

def stdBasis (i : Fin 4) : V4 := fun j => if i = j then 1 else 0

/--
  The Minkowski quadratic form with signature (+,+,+,-).
  Q(v) = v₀² + v₁² + v₂² - v₃²
-/
def minkowskiQ : QuadraticForm ℝ V4 :=
  QuadraticMap.weightedSumSquares ℝ ![1, 1, 1, -1]

theorem minkowskiQ_eval : ∀ v : V4, minkowskiQ v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2 := by
  intro v
  simp only [minkowskiQ, QuadraticMap.weightedSumSquares_apply]
  simp [Fin.sum_univ_four]
  ring

abbrev Cl31 := CliffordAlgebra minkowskiQ

/-! ## Basis Vectors -/

noncomputable def ι31 : V4 →ₗ[ℝ] Cl31 := CliffordAlgebra.ι minkowskiQ

noncomputable def e₁ : Cl31 := ι31 (stdBasis 0)
noncomputable def e₂ : Cl31 := ι31 (stdBasis 1)
noncomputable def e₃ : Cl31 := ι31 (stdBasis 2)
noncomputable def e₄ : Cl31 := ι31 (stdBasis 3)

/-! ## Fundamental Properties -/

theorem minkowskiQ_e1 : minkowskiQ (stdBasis 0) = 1 := by
  rw [minkowskiQ_eval]; simp [stdBasis]

theorem minkowskiQ_e2 : minkowskiQ (stdBasis 1) = 1 := by
  rw [minkowskiQ_eval]; simp [stdBasis]

theorem minkowskiQ_e3 : minkowskiQ (stdBasis 2) = 1 := by
  rw [minkowskiQ_eval]; simp [stdBasis]

theorem minkowskiQ_e4 : minkowskiQ (stdBasis 3) = -1 := by
  rw [minkowskiQ_eval]; simp [stdBasis]

theorem e₁_sq : e₁ * e₁ = 1 := by
  unfold e₁ ι31; rw [CliffordAlgebra.ι_sq_scalar, minkowskiQ_e1]; simp

theorem e₂_sq : e₂ * e₂ = 1 := by
  unfold e₂ ι31; rw [CliffordAlgebra.ι_sq_scalar, minkowskiQ_e2]; simp

theorem e₃_sq : e₃ * e₃ = 1 := by
  unfold e₃ ι31; rw [CliffordAlgebra.ι_sq_scalar, minkowskiQ_e3]; simp

theorem e₄_sq : e₄ * e₄ = -1 := by
  unfold e₄ ι31; rw [CliffordAlgebra.ι_sq_scalar, minkowskiQ_e4]; simp

/-! ## Bivectors -/

noncomputable def e₁₂ : Cl31 := e₁ * e₂
noncomputable def e₂₃ : Cl31 := e₂ * e₃
noncomputable def e₁₃ : Cl31 := e₁ * e₃

/-! ## Orthogonality -/

theorem stdBasis_add_sq (i j : Fin 4) (h : i ≠ j) (k : Fin 4) :
    ((stdBasis i + stdBasis j) k) ^ 2 = (stdBasis i k) ^ 2 + (stdBasis j k) ^ 2 := by
  simp only [stdBasis, Pi.add_apply]
  by_cases hi : i = k
  · simp only [hi, ↓reduceIte]
    by_cases hj : j = k
    · exact absurd (hi.trans hj.symm) h
    · simp only [hj, ↓reduceIte]; ring
  · simp only [hi, ↓reduceIte]
    by_cases hj : j = k
    · simp only [hj, ↓reduceIte]; ring
    · simp only [hj, ↓reduceIte]; ring

theorem stdBasis_ortho (i j : Fin 4) (h : i ≠ j) :
    QuadraticMap.IsOrtho minkowskiQ (stdBasis i) (stdBasis j) := by
  unfold QuadraticMap.IsOrtho
  rw [minkowskiQ_eval, minkowskiQ_eval, minkowskiQ_eval]
  simp only [Pi.add_apply]
  have h0 := stdBasis_add_sq i j h 0
  have h1 := stdBasis_add_sq i j h 1
  have h2 := stdBasis_add_sq i j h 2
  have h3 := stdBasis_add_sq i j h 3
  simp only [Pi.add_apply] at h0 h1 h2 h3
  linarith

theorem e₁_e₂_ortho : QuadraticMap.IsOrtho minkowskiQ (stdBasis 0) (stdBasis 1) :=
  stdBasis_ortho 0 1 (by decide)

theorem e₁_e₃_ortho : QuadraticMap.IsOrtho minkowskiQ (stdBasis 0) (stdBasis 2) :=
  stdBasis_ortho 0 2 (by decide)

theorem e₂_e₃_ortho : QuadraticMap.IsOrtho minkowskiQ (stdBasis 1) (stdBasis 2) :=
  stdBasis_ortho 1 2 (by decide)

theorem ortho_anticomm {v w : V4} (h : QuadraticMap.IsOrtho minkowskiQ v w) :
    ι31 v * ι31 w = -(ι31 w * ι31 v) := by
  unfold ι31
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h

theorem e₁_e₂_anticomm : e₁ * e₂ = -(e₂ * e₁) := by
  unfold e₁ e₂; exact ortho_anticomm e₁_e₂_ortho

theorem e₁_e₃_anticomm : e₁ * e₃ = -(e₃ * e₁) := by
  unfold e₁ e₃; exact ortho_anticomm e₁_e₃_ortho

theorem e₂_e₃_anticomm : e₂ * e₃ = -(e₃ * e₂) := by
  unfold e₂ e₃; exact ortho_anticomm e₂_e₃_ortho

theorem e₂_e₁_eq : e₂ * e₁ = -(e₁ * e₂) := by
  rw [e₁_e₂_anticomm, neg_neg]

theorem e₃_e₁_eq : e₃ * e₁ = -(e₁ * e₃) := by
  rw [e₁_e₃_anticomm, neg_neg]

theorem e₃_e₂_eq : e₃ * e₂ = -(e₂ * e₃) := by
  rw [e₂_e₃_anticomm, neg_neg]

/-! ## Bivector Properties -/

theorem e₁₂_sq : e₁₂ * e₁₂ = -1 := by
  unfold e₁₂
  calc e₁ * e₂ * (e₁ * e₂)
      = e₁ * (e₂ * (e₁ * e₂)) := by rw [mul_assoc]
    _ = e₁ * ((e₂ * e₁) * e₂) := by rw [mul_assoc]
    _ = e₁ * ((-(e₁ * e₂)) * e₂) := by rw [e₂_e₁_eq]
    _ = e₁ * (-(e₁ * e₂ * e₂)) := by rw [neg_mul]
    _ = e₁ * (-(e₁ * (e₂ * e₂))) := by rw [mul_assoc]
    _ = e₁ * (-(e₁ * 1)) := by rw [e₂_sq]
    _ = e₁ * (-e₁) := by rw [mul_one]
    _ = -(e₁ * e₁) := by rw [mul_neg]
    _ = -1 := by rw [e₁_sq]

theorem e₂₃_sq : e₂₃ * e₂₃ = -1 := by
  unfold e₂₃
  calc e₂ * e₃ * (e₂ * e₃)
      = e₂ * (e₃ * (e₂ * e₃)) := by rw [mul_assoc]
    _ = e₂ * ((e₃ * e₂) * e₃) := by rw [mul_assoc]
    _ = e₂ * ((-(e₂ * e₃)) * e₃) := by rw [e₃_e₂_eq]
    _ = e₂ * (-(e₂ * e₃ * e₃)) := by rw [neg_mul]
    _ = e₂ * (-(e₂ * (e₃ * e₃))) := by rw [mul_assoc]
    _ = e₂ * (-(e₂ * 1)) := by rw [e₃_sq]
    _ = e₂ * (-e₂) := by rw [mul_one]
    _ = -(e₂ * e₂) := by rw [mul_neg]
    _ = -1 := by rw [e₂_sq]

theorem e₁₃_sq : e₁₃ * e₁₃ = -1 := by
  unfold e₁₃
  calc e₁ * e₃ * (e₁ * e₃)
      = e₁ * (e₃ * (e₁ * e₃)) := by rw [mul_assoc]
    _ = e₁ * ((e₃ * e₁) * e₃) := by rw [mul_assoc]
    _ = e₁ * ((-(e₁ * e₃)) * e₃) := by rw [e₃_e₁_eq]
    _ = e₁ * (-(e₁ * e₃ * e₃)) := by rw [neg_mul]
    _ = e₁ * (-(e₁ * (e₃ * e₃))) := by rw [mul_assoc]
    _ = e₁ * (-(e₁ * 1)) := by rw [e₃_sq]
    _ = e₁ * (-e₁) := by rw [mul_one]
    _ = -(e₁ * e₁) := by rw [mul_neg]
    _ = -1 := by rw [e₁_sq]

/-! ## Rotor Operations -/

noncomputable def rotor₁₂ (θ : ℝ) : Cl31 :=
  algebraMap ℝ Cl31 (Real.cos (θ/2)) + algebraMap ℝ Cl31 (Real.sin (θ/2)) * e₁₂

noncomputable def rotor₂₃ (θ : ℝ) : Cl31 :=
  algebraMap ℝ Cl31 (Real.cos (θ/2)) + algebraMap ℝ Cl31 (Real.sin (θ/2)) * e₂₃

/-! ## Scalar-Clifford Interaction Lemmas -/

local notation "⟨" r "⟩" => algebraMap ℝ Cl31 r

theorem scalar_mul_comm (r : ℝ) (x : Cl31) : ⟨r⟩ * x = x * ⟨r⟩ :=
  Algebra.commutes r x

theorem scalar_mul_assoc (r : ℝ) (x y : Cl31) : ⟨r⟩ * (x * y) = (⟨r⟩ * x) * y := by
  rw [mul_assoc]

theorem scalar_mul_scalar (r s : ℝ) : ⟨r⟩ * ⟨s⟩ = ⟨r * s⟩ := by
  rw [← RingHom.map_mul]

theorem scalar_mul_e₁₂ (r : ℝ) : ⟨r⟩ * e₁₂ = e₁₂ * ⟨r⟩ := scalar_mul_comm r e₁₂

theorem scalar_add (r s : ℝ) : ⟨r⟩ + ⟨s⟩ = ⟨r + s⟩ := by
  rw [← RingHom.map_add]

/-! ## Rotor Multiplication (was axiom — now PROVED) -/

/--
  Rotor composition: the key identity for phase combination.
  (cos α + sin α * B) * (cos β + sin β * B) = cos(α+β) + sin(α+β) * B
  when B² = -1.

  Proof by expanding via distributivity, using scalar commutativity,
  B² = -1, and the angle addition formulas cos_add / sin_add.
-/
theorem rotor_mul_generic : ∀ (α β : ℝ) (B : Cl31), B * B = -1 →
    (⟨Real.cos α⟩ + ⟨Real.sin α⟩ * B) * (⟨Real.cos β⟩ + ⟨Real.sin β⟩ * B) =
    ⟨Real.cos (α + β)⟩ + ⟨Real.sin (α + β)⟩ * B := by
  intro α β B hB
  -- Expand the LHS using distributivity
  rw [mul_add, add_mul, add_mul]
  -- Simplify each of the four terms:
  -- Term 1: ⟨cos α⟩ * ⟨cos β⟩ = ⟨cos α * cos β⟩
  -- Term 2: ⟨cos α⟩ * (⟨sin β⟩ * B) = ⟨cos α * sin β⟩ * B
  -- Term 3: (⟨sin α⟩ * B) * ⟨cos β⟩ = ⟨sin α * cos β⟩ * B
  -- Term 4: (⟨sin α⟩ * B) * (⟨sin β⟩ * B) = -⟨sin α * sin β⟩
  have t1 : ⟨Real.cos α⟩ * ⟨Real.cos β⟩ = ⟨Real.cos α * Real.cos β⟩ :=
    scalar_mul_scalar _ _
  have t2 : ⟨Real.cos α⟩ * (⟨Real.sin β⟩ * B) = ⟨Real.cos α * Real.sin β⟩ * B := by
    rw [← mul_assoc, scalar_mul_scalar]
  have scalar_comm_B : ∀ r : ℝ, B * ⟨r⟩ = ⟨r⟩ * B :=
    fun r => (scalar_mul_comm r B).symm
  have t3 : ⟨Real.sin α⟩ * B * ⟨Real.cos β⟩ = ⟨Real.sin α * Real.cos β⟩ * B := by
    rw [mul_assoc, scalar_comm_B, ← mul_assoc, scalar_mul_scalar]
  have t4 : ⟨Real.sin α⟩ * B * (⟨Real.sin β⟩ * B) = ⟨-(Real.sin α * Real.sin β)⟩ := by
    set sa := ⟨Real.sin α⟩ with hsa_def
    set sb := ⟨Real.sin β⟩ with hsb_def
    -- Goal: sa * B * (sb * B) = ⟨-(sin α * sin β)⟩
    -- Step: rearrange to (sa * sb) * (B * B)
    have key : sa * B * (sb * B) = (sa * sb) * (B * B) := by
      -- sa * B * (sb * B) = sa * (B * (sb * B)) = sa * (B * sb * B)
      --   = sa * (sb * B * B) [since B * sb = sb * B]
      --   = sa * sb * (B * B) [by assoc]
      rw [mul_assoc sa B (sb * B)]
      conv_lhs => rw [← mul_assoc B sb B, show B * sb = sb * B from scalar_comm_B _,
                       mul_assoc sb B B]
      rw [← mul_assoc sa sb (B * B)]
    rw [key, hsa_def, hsb_def, scalar_mul_scalar, hB, mul_neg_one]
    exact (RingHom.map_neg (algebraMap ℝ Cl31) _).symm
  rw [t1, t2, t3, t4]
  rw [Real.cos_add, Real.sin_add]
  simp only [map_sub, map_add, map_neg, add_mul]
  abel

theorem rotor₁₂_mul (α β : ℝ) : rotor₁₂ α * rotor₁₂ β = rotor₁₂ (α + β) := by
  unfold rotor₁₂
  have h1 : (α + β) / 2 = α / 2 + β / 2 := by ring
  rw [h1]
  exact rotor_mul_generic (α/2) (β/2) e₁₂ e₁₂_sq

theorem rotor₂₃_mul (α β : ℝ) : rotor₂₃ α * rotor₂₃ β = rotor₂₃ (α + β) := by
  unfold rotor₂₃
  have h1 : (α + β) / 2 = α / 2 + β / 2 := by ring
  rw [h1]
  exact rotor_mul_generic (α/2) (β/2) e₂₃ e₂₃_sq

theorem rotor₁₂_zero : rotor₁₂ 0 = 1 := by
  unfold rotor₁₂; simp [Real.cos_zero, Real.sin_zero]

/-! ## Hadamard Element -/

noncomputable def hadamardElement : Cl31 :=
  algebraMap ℝ Cl31 (1 / Real.sqrt 2) * (e₁ + e₃)

/--
  Hadamard squared equals identity (was axiom — now PROVED).

  Proof: (c(e₁+e₃))² = c²(e₁+e₃)² = c²(e₁²+e₁e₃+e₃e₁+e₃²)
  where c = 1/√2. Since e₁ and e₃ are orthogonal, e₁e₃+e₃e₁=0.
  So = c²(1+1) = (1/2)(2) = 1.
-/
theorem hadamard_sq : hadamardElement * hadamardElement = 1 := by
  unfold hadamardElement
  set c := algebraMap ℝ Cl31 (1 / Real.sqrt 2)
  set w := e₁ + e₃
  have hvc : w * c = c * w := (scalar_mul_comm _ w).symm
  -- Rearrange c*w*(c*w) to c*c*(w*w)
  have step1 : c * w * (c * w) = (c * c) * (w * w) := by
    calc c * w * (c * w)
        = c * (w * (c * w)) := by rw [mul_assoc]
      _ = c * ((w * c) * w) := by rw [mul_assoc]
      _ = c * ((c * w) * w) := by rw [hvc]
      _ = c * (c * (w * w)) := by rw [mul_assoc]
      _ = (c * c) * (w * w) := by rw [← mul_assoc]
  -- w*w = (e₁+e₃)² = 1 + 1
  have hv_sq : w * w = (1 : Cl31) + 1 := by
    change (e₁ + e₃) * (e₁ + e₃) = 1 + 1
    rw [mul_add, add_mul, add_mul, e₁_sq, e₃_sq, e₃_e₁_eq]
    abel
  -- c*c = algebraMap(1/√2 * 1/√2)
  have hc_sq : c * c = algebraMap ℝ Cl31 (1 / Real.sqrt 2 * (1 / Real.sqrt 2)) :=
    scalar_mul_scalar _ _
  rw [step1, hv_sq, hc_sq]
  have h1_plus_1 : (1 : Cl31) + 1 = algebraMap ℝ Cl31 2 := by
    rw [← map_one (algebraMap ℝ Cl31), ← map_add (algebraMap ℝ Cl31)]
    norm_num
  rw [h1_plus_1, ← map_mul (algebraMap ℝ Cl31), ← map_one (algebraMap ℝ Cl31)]
  congr 1
  have h2pos : (0 : ℝ) < 2 := by norm_num
  field_simp
  rw [sq, Real.mul_self_sqrt h2pos.le]

/-! ## Reversal (Dagger) Operation -/

noncomputable def rev : Cl31 →ₗ[ℝ] Cl31 := CliffordAlgebra.reverse

theorem rev_rev (x : Cl31) : rev (rev x) = x := CliffordAlgebra.reverse_reverse x

theorem rev_mul (x y : Cl31) : rev (x * y) = rev y * rev x := by
  unfold rev; exact CliffordAlgebra.reverse.map_mul x y

end ZXClifford.Foundation
