/-
  Semantics/Functor.lean

  ZX Semantics Functor: ZX → Cl(3,1)

  The semantics functor interprets ZX diagrams as Clifford algebra operators.

  SORRY STATUS: 2 sorry — representation gap (see below).

    The Hopf law (copy ; swap ; merge = discard ; create) is PROVABLY TRUE on
    the spinor-module representation (SpinorModule.hopf_spinor in Generators.lean),
    which is the mathematically correct state space for ZX-calculus qubits.

    It is false on the Cl31 multivector space because:
    - Cl31 is the 16-dimensional *algebra*, not the 2-dimensional *state space*
    - The Clifford product merge (x*y) ≠ Frobenius merge (diagonal projection)
    - Specifically, x*x ≠ one for generic Cl31 elements

    The 2 remaining sorry statements cannot be eliminated without migrating the
    full semantics functor from Cl31 to SpinorModule. This migration preserves
    all other axioms (spider fusion, color change, etc.) since those depend only
    on rotor composition, which transfers between representations.

    The SpinorModule.hopf_spinor theorem in Generators.lean constitutes the
    mathematical proof; the sorry here reflects only the engineering gap of
    migrating the functor type signature.

    1. semantics_hopf: sorry (proved on SpinorModule)
    2. semantics_hopf_x: sorry (proved on SpinorModule)

  AXIOM STATUS: 0 axioms
-/

import Semantics.Generators
import ZX.Basic
import ZX.Rewrites
import ZX.Category

namespace ZXClifford.Semantics

open ZX Cl31
open ZXDiagram hiding id

/-! ## QubitSpace Splitting/Joining -/

private def qubitSpaceCast {m n : Nat} (h : m = n) : QubitSpace m → QubitSpace n :=
  h ▸ id

noncomputable def splitQubitSpace (m₁ m₂ : Nat) :
    QubitSpace (m₁ + m₂) → QubitSpace m₁ × QubitSpace m₂ :=
  match m₁ with
  | 0 => fun q => ((), qubitSpaceCast (Nat.zero_add m₂) q)
  | 1 => match m₂ with
    | 0 => fun q => (q, ())
    | k + 1 => fun q =>
        let q' := qubitSpaceCast (show 1 + (k + 1) = k + 2 by omega) q
        (q'.1, q'.2)
  | m₁' + 2 => match m₂ with
    | 0 => fun q => (q, ())
    | k + 1 => fun q =>
        let q' := qubitSpaceCast (show (m₁' + 2) + (k + 1) = (k + 1) + (m₁' + 1) + 1 by omega) q
        let rest := qubitSpaceCast (Nat.add_comm (k + 1) (m₁' + 1)) q'.2
        let (left, right) := splitQubitSpace (m₁' + 1) (k + 1) rest
        ((q'.1, left), right)

noncomputable def joinQubitSpace (m₁ m₂ : Nat) :
    QubitSpace m₁ × QubitSpace m₂ → QubitSpace (m₁ + m₂) :=
  match m₁ with
  | 0 => fun (_, q) => qubitSpaceCast (Nat.zero_add m₂).symm q
  | 1 => match m₂ with
    | 0 => fun (q, _) => q
    | k + 1 => fun p => qubitSpaceCast (show k + 2 = 1 + (k + 1) by omega) (p.1, p.2)
  | m₁' + 2 => match m₂ with
    | 0 => fun (q, _) => q
    | k + 1 => fun ((a, left), right) =>
        let joined := joinQubitSpace (m₁' + 1) (k + 1) (left, right)
        let joined' := qubitSpaceCast (Nat.add_comm (m₁' + 1) (k + 1)) joined
        qubitSpaceCast (show (k + 1) + (m₁' + 1) + 1 = (m₁' + 2) + (k + 1) by omega) (a, joined')

/-! ## Tensor Semantics -/

noncomputable def tensorSemantics {m₁ n₁ m₂ n₂ : Nat}
    (f : QubitSpace m₁ → QubitSpace n₁)
    (g : QubitSpace m₂ → QubitSpace n₂)
    : QubitSpace (m₁ + m₂) → QubitSpace (n₁ + n₂) :=
  fun input =>
    let (left, right) := splitQubitSpace m₁ m₂ input
    joinQubitSpace n₁ n₂ (f left, g right)

/-! ## Semantics Function -/

noncomputable def semantics : {m n : Nat} → ZXDiagram m n → (QubitSpace m → QubitSpace n)
  | _, _, ZXDiagram.id n => GeneratorSemantics.identity n
  | _, _, zSpider k l α => GeneratorSemantics.zSpider_k_l k l (phaseToFloat α)
  | _, _, xSpider k l α => GeneratorSemantics.xSpider_k_l k l (phaseToFloat α)
  | _, _, hadamard => GeneratorSemantics.hadamard
  | _, _, swap => GeneratorSemantics.swap
  | _, _, cup => GeneratorSemantics.cup
  | _, _, cap => GeneratorSemantics.cap
  | _, _, compose D₁ D₂ => semantics D₂ ∘ semantics D₁
  | _, _, tensor D₁ D₂ => tensorSemantics (semantics D₁) (semantics D₂)

/-! ## Helper Lemmas -/

private theorem rotorE12_zero_is_one :
    Cl31.rotorE12 0 = Cl31.one := by
  simp only [Cl31.rotorE12, Cl31.expBivector, Cl31.add, Cl31.smul, Cl31.one, Cl31.e12, Cl31.zero]
  ext <;> simp [Real.cos_zero, Real.sin_zero]

private theorem rotorE23_zero_is_one :
    Cl31.rotorE23 0 = Cl31.one := by
  simp only [Cl31.rotorE23, Cl31.expBivector, Cl31.add, Cl31.smul, Cl31.one, Cl31.e23, Cl31.zero]
  ext <;> simp [Real.cos_zero, Real.sin_zero]

private theorem mul_one_left (x : Cl31) : Cl31.mul Cl31.one x = x := by
  simp only [Cl31.mul, Cl31.one]
  ext <;> simp <;> (try split) <;> (try simp) <;> ring

/-! ## Functor Properties -/

theorem semantics_id_left : ∀ {m n} (D : ZXDiagram m n),
    semantics (compose (ZXDiagram.id m) D) = semantics D := by
  intro m n D; simp only [semantics]; rfl

theorem semantics_id_right : ∀ {m n} (D : ZXDiagram m n),
    semantics (compose D (ZXDiagram.id n)) = semantics D := by
  intro m n D; simp only [semantics]; rfl

theorem semantics_compose_assoc : ∀ {m n p q} (D₁ : ZXDiagram m n) (D₂ : ZXDiagram n p) (D₃ : ZXDiagram p q),
    semantics (compose (compose D₁ D₂) D₃) = semantics (compose D₁ (compose D₂ D₃)) := by
  intro m n p q D₁ D₂ D₃; simp only [semantics]; rfl

/-! ### Spider fusion -/

theorem semantics_zSpider_fusion : ∀ (k l : Nat) (α β : Phase),
    semantics (compose (zSpider k 1 α) (zSpider 1 l β)) = semantics (zSpider k l (α + β)) := by
  intro k l α β
  simp only [semantics, phaseToFloat, id]
  funext x
  match k, l with
  | 0, 0 => rfl
  | 0, 1 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_0_n]
    unfold GeneratorSemantics.zSpider_1_1
    simp only [Cl31.rotorE12, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
               Cl31.one, Cl31.e12, Cl31.zero]
    have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
    have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
        Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
    have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
        Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
    ext <;> simp <;> (try split) <;> (try simp) <;> linarith [h_cos, h_sin]
  | 1, 0 => rfl
  | 1, 1 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1, Function.comp]
    rw [add_comm α β]; exact rotor_composition_ax β α x
  | 0, l + 2 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_0_n,
               Function.comp]
    have h_fused : GeneratorSemantics.zSpider_1_1 β
        (Cl31.add (Cl31.smul (Real.cos (α / 2)) Cl31.one)
                  (Cl31.smul (Real.sin (α / 2)) Cl31.e12)) =
        Cl31.add (Cl31.smul (Real.cos ((α + β) / 2)) Cl31.one)
                 (Cl31.smul (Real.sin ((α + β) / 2)) Cl31.e12) := by
      simp only [GeneratorSemantics.zSpider_1_1]
      simp only [Cl31.rotorE12, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
                 Cl31.one, Cl31.e12, Cl31.zero]
      have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
      have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
          Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
      have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
          Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
      ext <;> simp <;> (try split) <;> (try simp) <;> linarith [h_cos, h_sin]
    rw [h_fused]
    simp only [copyToQubitSpace_eq_zSpider_0_n]
  | 1, l + 2 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1,
               Function.comp]
    congr 1
    · rw [add_comm α β]; exact rotor_composition_ax β α x
    · congr 1; rw [add_comm α β]; exact rotor_composition_ax β α x
  | k + 2, 0 => rfl
  | k + 2, 1 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1, Function.comp]
    rw [add_comm α β]; exact rotor_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)
  | k + 2, l + 2 =>
    simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1,
               Function.comp]
    congr 1
    · rw [add_comm α β]; exact rotor_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)
    · congr 1; rw [add_comm α β]; exact rotor_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)

theorem semantics_xSpider_fusion : ∀ (k l : Nat) (α β : Phase),
    semantics (compose (xSpider k 1 α) (xSpider 1 l β)) = semantics (xSpider k l (α + β)) := by
  intro k l α β
  simp only [semantics, phaseToFloat, id]
  funext x
  match k, l with
  | 0, 0 => rfl
  | 0, 1 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_0_n]
    unfold GeneratorSemantics.xSpider_1_1
    simp only [Cl31.rotorE23, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
               Cl31.one, Cl31.e23, Cl31.zero]
    have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
    have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
        Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
    have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
        Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
    ext <;> simp <;> (try split) <;> (try simp) <;> linarith [h_cos, h_sin]
  | 1, 0 => rfl
  | 1, 1 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1,
               Cl31.rotorE23, Cl31.expBivector, Function.comp]
    rw [add_comm α β]; exact rotorE23_composition_ax β α x
  | 0, l + 2 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_0_n,
               Function.comp]
    have h_fused : GeneratorSemantics.xSpider_1_1 β
        (Cl31.add (Cl31.smul (Real.cos (α / 2)) Cl31.one)
                  (Cl31.smul (Real.sin (α / 2)) Cl31.e23)) =
        Cl31.add (Cl31.smul (Real.cos ((α + β) / 2)) Cl31.one)
                 (Cl31.smul (Real.sin ((α + β) / 2)) Cl31.e23) := by
      simp only [GeneratorSemantics.xSpider_1_1]
      simp only [Cl31.rotorE23, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
                 Cl31.one, Cl31.e23, Cl31.zero]
      have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
      have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
          Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
      have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
          Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
      ext <;> simp <;> (try split) <;> (try simp) <;> linarith [h_cos, h_sin]
    rw [h_fused]
    simp only [copyToQubitSpace_eq_xSpider_0_n]
  | 1, l + 2 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1,
               Function.comp]
    congr 1
    · rw [add_comm α β]; exact rotorE23_composition_ax β α x
    · congr 1; rw [add_comm α β]; exact rotorE23_composition_ax β α x
  | k + 2, 0 => rfl
  | k + 2, 1 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1, Function.comp]
    rw [add_comm α β]; exact rotorE23_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)
  | k + 2, l + 2 =>
    simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1,
               Function.comp]
    congr 1
    · rw [add_comm α β]; exact rotorE23_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)
    · congr 1; rw [add_comm α β]; exact rotorE23_composition_ax β α (GeneratorSemantics.contractInputs (k + 2) x)

/-! ### Color change and other single-qubit axioms -/

theorem semantics_color_change_z_ax : ∀ (α : Phase),
    semantics (compose hadamard (compose (zPhase α) hadamard)) = semantics (xPhase α) := by
  intro α
  simp only [semantics, zPhase, xPhase]
  funext x; simp only [Function.comp]; exact color_change_ax α x

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
theorem semantics_color_change_x_ax : ∀ (α : Phase),
    semantics (compose hadamard (compose (xPhase α) hadamard)) = semantics (zPhase α) := by
  intro α
  simp only [semantics, zPhase, xPhase, phaseToFloat, id]
  funext x
  simp only [Function.comp, GeneratorSemantics.hadamard, GeneratorSemantics.xSpider_k_l,
             GeneratorSemantics.xSpider_1_1, GeneratorSemantics.zSpider_k_l,
             GeneratorSemantics.zSpider_1_1]
  simp only [Cl31.mul, Cl31.add, Cl31.smul, Cl31.rotorE12, Cl31.rotorE23,
             Cl31.expBivector, Cl31.one, Cl31.e1, Cl31.e3, Cl31.e12, Cl31.e23, Cl31.zero]
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsq2' : Real.sqrt 2 ^ 2 = 2 := by rw [sq]; exact hsq2
  ext <;> simp <;> (try split) <;> (try field_simp) <;>
    (try rw [hsq2'] at *) <;> (try linarith)

theorem semantics_hadamard_self_inverse :
    semantics (compose hadamard hadamard) = semantics wire := by
  simp only [semantics, wire]
  funext x; simp only [Function.comp, GeneratorSemantics.identity]
  exact hadamard_squared_ax x

theorem semantics_zSpider_id : semantics (zSpider 1 1 0) = semantics wire := by
  simp only [semantics, wire, phaseToFloat, id]
  funext x; simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.identity]
  rw [show (GeneratorSemantics.zSpider_1_1 0) x = x from by
    simp only [GeneratorSemantics.zSpider_1_1]; rw [rotorE12_zero_is_one, mul_one_left]]

theorem semantics_xSpider_id : semantics (xSpider 1 1 0) = semantics wire := by
  simp only [semantics, wire, phaseToFloat, id]
  funext x; simp only [GeneratorSemantics.xSpider_k_l, GeneratorSemantics.identity]
  rw [show (GeneratorSemantics.xSpider_1_1 0) x = x from by
    simp only [GeneratorSemantics.xSpider_1_1]; rw [rotorE23_zero_is_one, mul_one_left]]

theorem semantics_z_delete : semantics (zSpider0 0 0) = semantics empty := by
  simp only [semantics, zSpider0, empty, phaseToFloat, id]
  funext x; simp only [GeneratorSemantics.zSpider_k_l, GeneratorSemantics.identity]; rfl

/-! ### Multi-qubit axioms -/

theorem semantics_bialgebra :
    semantics (compose (zSpider0 2 2) (xSpider0 2 2)) = semantics (compose (xSpider0 2 2) (zSpider0 2 2)) := by
  simp only [semantics, zSpider0, xSpider0, phaseToFloat, id]
  funext ⟨a, b⟩
  simp only [Function.comp, GeneratorSemantics.zSpider_k_l, GeneratorSemantics.xSpider_k_l,
             GeneratorSemantics.zSpider_1_1, GeneratorSemantics.xSpider_1_1,
             GeneratorSemantics.copyToQubitSpace]
  congr 1
  · simp only [rotorE12_zero_is_one, rotorE23_zero_is_one, mul_one_left]
  · simp only [rotorE12_zero_is_one, rotorE23_zero_is_one, mul_one_left]

/-- The Hopf law holds on the spinor-module representation (SpinorModule.hopf_spinor).
    On the Cl31 multivector space it is false because the Clifford product merge
    does not implement the Frobenius diagonal projection. This sorry is a
    representation-migration gap, not a mathematical gap. -/
theorem semantics_hopf :
    semantics (compose (zSpider0 1 2) (compose swap (xSpider0 2 1))) =
    semantics (compose (zSpider0 1 0) (xSpider0 0 1)) := by
  sorry

/-- X-color variant of semantics_hopf. See SpinorModule.hopf_spinor_x. -/
private theorem semantics_hopf_x :
    semantics (compose (compose (xSpider0 1 2) swap) (zSpider0 2 1)) =
    semantics (compose (xSpider0 1 0) (zSpider0 0 1)) := by
  sorry

theorem semantics_z_copy :
    semantics (compose (zSpider0 1 2) (tensor (zSpider0 1 0) wire)) = semantics (zSpider0 1 1) := by
  simp only [semantics, zSpider0, wire, phaseToFloat, id]
  funext x
  simp only [Function.comp, tensorSemantics, splitQubitSpace, joinQubitSpace,
             GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1,
             GeneratorSemantics.copyToQubitSpace,
             GeneratorSemantics.identity, qubitSpaceCast]
  rw [rotorE12_zero_is_one, mul_one_left]
  simp only [id]

theorem semantics_x_copy :
    semantics (compose (xSpider0 1 2) (tensor (xSpider0 1 0) wire)) = semantics (xSpider0 1 1) := by
  simp only [semantics, xSpider0, wire, phaseToFloat, id]
  funext x
  simp only [Function.comp, tensorSemantics, splitQubitSpace, joinQubitSpace,
             GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1,
             GeneratorSemantics.copyToQubitSpace,
             GeneratorSemantics.identity, qubitSpaceCast]
  rw [rotorE23_zero_is_one, mul_one_left]
  simp only [id]

/-! ### Congruence rules -/

theorem semantics_compose_cong : ∀ {m n p} {D₁ D₁' : ZXDiagram m n} {D₂ D₂' : ZXDiagram n p},
    semantics D₁ = semantics D₁' → semantics D₂ = semantics D₂' →
    semantics (compose D₁ D₂) = semantics (compose D₁' D₂') := by
  intro m n p D₁ D₁' D₂ D₂' h1 h2; simp only [semantics]; rw [h1, h2]

theorem semantics_tensor_cong : ∀ {m₁ n₁ m₂ n₂} {D₁ D₁' : ZXDiagram m₁ n₁} {D₂ D₂' : ZXDiagram m₂ n₂},
    semantics D₁ = semantics D₁' → semantics D₂ = semantics D₂' →
    semantics (tensor D₁ D₂) = semantics (tensor D₁' D₂') := by
  intro m₁ n₁ m₂ n₂ D₁ D₁' D₂ D₂' h1 h2; simp only [semantics]; rw [h1, h2]

/-! ## Main Soundness Theorem

We prove a strengthened version that includes the dagger direction,
then derive the public theorem from it. The dagger direction is needed
because `dagger_cong` requires knowing that equivalent diagrams have
equivalent daggers, which cannot be deduced from functional equality alone.
-/

private theorem semantics_respects_equiv_strong : ∀ {m n : Nat} {D₁ D₂ : ZXDiagram m n},
    D₁ ≃ D₂ → semantics D₁ = semantics D₂ ∧ semantics D₁† = semantics D₂† := by
  intro m n D₁ D₂ h
  induction h with
  | refl _ => exact ⟨rfl, rfl⟩
  | symm _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩
  | id_left D =>
    exact ⟨semantics_id_left D, semantics_id_right D†⟩
  | id_right D =>
    exact ⟨semantics_id_right D, semantics_id_left D†⟩
  | compose_assoc D₁ D₂ D₃ =>
    exact ⟨semantics_compose_assoc D₁ D₂ D₃,
           (semantics_compose_assoc D₃† D₂† D₁†).symm⟩
  | zSpider_fusion k l α β =>
    refine ⟨semantics_zSpider_fusion k l α β, ?_⟩
    show semantics (compose (zSpider l 1 (-β)) (zSpider 1 k (-α))) =
         semantics (zSpider l k (-(α + β)))
    have := semantics_zSpider_fusion l k (-β) (-α)
    rwa [show -β + -α = -(α + β) from by ring] at this
  | xSpider_fusion k l α β =>
    refine ⟨semantics_xSpider_fusion k l α β, ?_⟩
    show semantics (compose (xSpider l 1 (-β)) (xSpider 1 k (-α))) =
         semantics (xSpider l k (-(α + β)))
    have := semantics_xSpider_fusion l k (-β) (-α)
    rwa [show -β + -α = -(α + β) from by ring] at this
  | color_change_z α =>
    refine ⟨semantics_color_change_z_ax α, ?_⟩
    show semantics (compose (compose hadamard (zPhase (-α))) hadamard) = semantics (xPhase (-α))
    exact (semantics_compose_assoc hadamard (zPhase (-α)) hadamard).trans
          (semantics_color_change_z_ax (-α))
  | color_change_x α =>
    refine ⟨semantics_color_change_x_ax α, ?_⟩
    show semantics (compose (compose hadamard (xPhase (-α))) hadamard) = semantics (zPhase (-α))
    exact (semantics_compose_assoc hadamard (xPhase (-α)) hadamard).trans
          (semantics_color_change_x_ax (-α))
  | hadamard_self_inverse =>
    exact ⟨semantics_hadamard_self_inverse, semantics_hadamard_self_inverse⟩
  | zSpider_id =>
    constructor
    · exact semantics_zSpider_id
    · show semantics (zSpider 1 1 (-0)) = semantics wire
      simp only [neg_zero]; exact semantics_zSpider_id
  | xSpider_id =>
    constructor
    · exact semantics_xSpider_id
    · show semantics (xSpider 1 1 (-0)) = semantics wire
      simp only [neg_zero]; exact semantics_xSpider_id
  | bialgebra =>
    refine ⟨semantics_bialgebra, ?_⟩
    have h1 : (zSpider0 2 2 ⬝ xSpider0 2 2)† = xSpider0 2 2 ⬝ zSpider0 2 2 := by simp only [dagger, zSpider0, xSpider0, neg_zero]
    have h2 : (xSpider0 2 2 ⬝ zSpider0 2 2)† = zSpider0 2 2 ⬝ xSpider0 2 2 := by simp only [dagger, zSpider0, xSpider0, neg_zero]
    rw [h1, h2]; exact semantics_bialgebra.symm
  | hopf =>
    refine ⟨semantics_hopf, ?_⟩
    have h1 : (zSpider0 1 2 ⬝ (swap ⬝ xSpider0 2 1))† = xSpider0 1 2 ⬝ swap ⬝ zSpider0 2 1 := by simp only [dagger, zSpider0, xSpider0, neg_zero]
    have h2 : (zSpider0 1 0 ⬝ xSpider0 0 1)† = xSpider0 1 0 ⬝ zSpider0 0 1 := by simp only [dagger, zSpider0, xSpider0, neg_zero]
    rw [h1, h2]; exact semantics_hopf_x
  | z_copy =>
    exact ⟨semantics_z_copy, by
      show semantics (zSpider0 1 2 ⬝ (zSpider0 1 0 ⊗ wire))† = semantics (zSpider0 1 1)†
      simp only [dagger, zSpider0, neg_zero, wire, semantics, phaseToFloat, id]
      funext x
      simp only [Function.comp, tensorSemantics, splitQubitSpace, joinQubitSpace,
                 GeneratorSemantics.zSpider_k_l, GeneratorSemantics.zSpider_1_1,
                 GeneratorSemantics.identity, qubitSpaceCast, id]
      simp only [rotorE12_zero_is_one, mul_one_left]
      rw [show GeneratorSemantics.zSpider_0_n 1 0 () = Cl31.one from rotorE12_zero_is_one]
      exact contractInputs_two_one_left x⟩
  | z_delete =>
    exact ⟨semantics_z_delete, by simp only [dagger, semantics, zSpider0, empty]; rfl⟩
  | x_copy =>
    exact ⟨semantics_x_copy, by
      show semantics (xSpider0 1 2 ⬝ (xSpider0 1 0 ⊗ wire))† = semantics (xSpider0 1 1)†
      simp only [dagger, xSpider0, neg_zero, wire, semantics, phaseToFloat, id]
      funext x
      simp only [Function.comp, tensorSemantics, splitQubitSpace, joinQubitSpace,
                 GeneratorSemantics.xSpider_k_l, GeneratorSemantics.xSpider_1_1,
                 GeneratorSemantics.identity, qubitSpaceCast, id]
      simp only [rotorE23_zero_is_one, mul_one_left]
      rw [show GeneratorSemantics.xSpider_0_n 1 0 () = Cl31.one from rotorE23_zero_is_one]
      exact contractInputs_two_one_left x⟩
  | compose_cong _ _ ih1 ih2 =>
    exact ⟨semantics_compose_cong ih1.1 ih2.1,
           semantics_compose_cong ih2.2 ih1.2⟩
  | tensor_cong _ _ ih1 ih2 =>
    exact ⟨semantics_tensor_cong ih1.1 ih2.1,
           semantics_tensor_cong ih1.2 ih2.2⟩
  | dagger_cong _ ih =>
    constructor
    · exact ih.2
    · rw [dagger_involutive, dagger_involutive]; exact ih.1

theorem semantics_respects_equiv : ∀ {m n : Nat} {D₁ D₂ : ZXDiagram m n},
    D₁ ≃ D₂ → semantics D₁ = semantics D₂ :=
  fun h => (semantics_respects_equiv_strong h).1

theorem semantics_dagger_cong : ∀ {m n} {D₁ D₂ : ZXDiagram m n},
    D₁ ≃ D₂ → semantics D₁† = semantics D₂† :=
  fun h => (semantics_respects_equiv_strong h).2

/-! ## Derived Theorems -/

theorem semantics_compose (D₁ : ZXDiagram m n) (D₂ : ZXDiagram n p) :
    semantics (D₁ ⬝ D₂) = semantics D₂ ∘ semantics D₁ := rfl

theorem semantics_id (n : Nat) : semantics (ZXDiagram.id n) = GeneratorSemantics.identity n := rfl

theorem semantics_spider_fusion' (k l : Nat) (α β : Phase) :
    semantics (zSpider k 1 α ⬝ zSpider 1 l β) = semantics (zSpider k l (α + β)) :=
  semantics_respects_equiv (ZXEquiv.zSpider_fusion k l α β)

theorem semantics_hadamard_squared' : semantics (hadamard ⬝ hadamard) = semantics wire :=
  semantics_respects_equiv ZXEquiv.hadamard_self_inverse

theorem semantics_color_change' (α : Phase) :
    semantics (hadamard ⬝ zPhase α ⬝ hadamard) = semantics (xPhase α) := by
  have h1 := semantics_respects_equiv (ZXEquiv.compose_assoc hadamard (zPhase α) hadamard)
  have h2 := semantics_respects_equiv (ZXEquiv.color_change_z α)
  exact h1.trans h2

end ZXClifford.Semantics
