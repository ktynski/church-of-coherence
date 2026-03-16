/-
  ZX/Rewrites.lean
  
  ZX-Calculus Rewrite Rules
  
  Defines ZXEquiv as an inductive relation capturing all ZX rewrite rules.
  This enables formal proofs of equivalence preservation.
-/

import ZX.Basic

namespace ZXClifford.ZX

open ZXDiagram

/-! ## ZX Equivalence as Inductive Relation -/

/-- 
  ZX equivalence relation defined inductively.
  Two diagrams are equivalent if connected by a sequence of rewrites.
-/
inductive ZXEquiv : {m n : Nat} → ZXDiagram m n → ZXDiagram m n → Prop
  -- Equivalence relation axioms
  | refl : ∀ {m n} (D : ZXDiagram m n), ZXEquiv D D
  | symm : ∀ {m n} {D₁ D₂ : ZXDiagram m n}, ZXEquiv D₁ D₂ → ZXEquiv D₂ D₁
  | trans : ∀ {m n} {D₁ D₂ D₃ : ZXDiagram m n}, 
            ZXEquiv D₁ D₂ → ZXEquiv D₂ D₃ → ZXEquiv D₁ D₃
  
  -- Category axioms
  | id_left : ∀ {m n} (D : ZXDiagram m n), ZXEquiv (compose (id m) D) D
  | id_right : ∀ {m n} (D : ZXDiagram m n), ZXEquiv (compose D (id n)) D
  | compose_assoc : ∀ {m n p q} (D₁ : ZXDiagram m n) (D₂ : ZXDiagram n p) (D₃ : ZXDiagram p q),
                    ZXEquiv (compose (compose D₁ D₂) D₃) (compose D₁ (compose D₂ D₃))
  
  -- Spider fusion
  | zSpider_fusion : ∀ (k l : Nat) (α β : Phase),
                     ZXEquiv (compose (zSpider k 1 α) (zSpider 1 l β)) (zSpider k l (α + β))
  | xSpider_fusion : ∀ (k l : Nat) (α β : Phase),
                     ZXEquiv (compose (xSpider k 1 α) (xSpider 1 l β)) (xSpider k l (α + β))
  
  -- Color change (Hadamard conjugation)
  | color_change_z : ∀ (α : Phase),
                     ZXEquiv (compose hadamard (compose (zPhase α) hadamard)) (xPhase α)
  | color_change_x : ∀ (α : Phase),
                     ZXEquiv (compose hadamard (compose (xPhase α) hadamard)) (zPhase α)
  
  -- Hadamard self-inverse
  | hadamard_self_inverse : ZXEquiv (compose hadamard hadamard) wire
  
  -- Spider identities (0-phase spiders are identities)
  | zSpider_id : ZXEquiv (zSpider 1 1 0) wire
  | xSpider_id : ZXEquiv (xSpider 1 1 0) wire
  
  -- Bialgebra (simplified - same-color interaction)
  | bialgebra : ZXEquiv (compose (zSpider0 2 2) (xSpider0 2 2)) 
                        (compose (xSpider0 2 2) (zSpider0 2 2))
  
  -- Hopf law
  | hopf : ZXEquiv (compose (zSpider0 1 2) (compose swap (xSpider0 2 1)))
                   (compose (zSpider0 1 0) (xSpider0 0 1))
  
  -- Copy rules
  | z_copy : ZXEquiv (compose (zSpider0 1 2) (tensor (zSpider0 1 0) wire)) (zSpider0 1 1)
  | z_delete : ZXEquiv (zSpider0 0 0) empty
  | x_copy : ZXEquiv (compose (xSpider0 1 2) (tensor (xSpider0 1 0) wire)) (xSpider0 1 1)
  
  -- Congruence rules (rewriting under contexts)
  | compose_cong : ∀ {m n p} {D₁ D₁' : ZXDiagram m n} {D₂ D₂' : ZXDiagram n p},
                   ZXEquiv D₁ D₁' → ZXEquiv D₂ D₂' → ZXEquiv (compose D₁ D₂) (compose D₁' D₂')
  | tensor_cong : ∀ {m₁ n₁ m₂ n₂} {D₁ D₁' : ZXDiagram m₁ n₁} {D₂ D₂' : ZXDiagram m₂ n₂},
                  ZXEquiv D₁ D₁' → ZXEquiv D₂ D₂' → ZXEquiv (tensor D₁ D₂) (tensor D₁' D₂')
  | dagger_cong : ∀ {m n} {D₁ D₂ : ZXDiagram m n}, ZXEquiv D₁ D₂ → ZXEquiv D₁† D₂†

/-- Notation for ZX equivalence -/
scoped infix:50 " ≃ " => ZXEquiv

-- Instances for calc syntax
instance : Trans (@ZXEquiv m n) (@ZXEquiv m n) (@ZXEquiv m n) where
  trans := ZXEquiv.trans

namespace ZXEquiv

/-! ## Derived Equivalences -/

/-- Left congruence for composition -/
theorem compose_cong_left {m n p : Nat} {D₁ D₁' : ZXDiagram m n} (D₂ : ZXDiagram n p) 
    (h : D₁ ≃ D₁') : compose D₁ D₂ ≃ compose D₁' D₂ := 
  compose_cong h (refl D₂)

/-- Right congruence for composition -/
theorem compose_cong_right {m n p : Nat} (D₁ : ZXDiagram m n) {D₂ D₂' : ZXDiagram n p}
    (h : D₂ ≃ D₂') : compose D₁ D₂ ≃ compose D₁ D₂' := 
  compose_cong (refl D₁) h

/-- Left congruence for tensor -/
theorem tensor_cong_left {m₁ n₁ m₂ n₂ : Nat} {D₁ D₁' : ZXDiagram m₁ n₁} (D₂ : ZXDiagram m₂ n₂)
    (h : D₁ ≃ D₁') : tensor D₁ D₂ ≃ tensor D₁' D₂ := 
  tensor_cong h (refl D₂)

/-- Right congruence for tensor -/
theorem tensor_cong_right {m₁ n₁ m₂ n₂ : Nat} (D₁ : ZXDiagram m₁ n₁) {D₂ D₂' : ZXDiagram m₂ n₂}
    (h : D₂ ≃ D₂') : tensor D₁ D₂ ≃ tensor D₁ D₂' := 
  tensor_cong (refl D₁) h

/-- Phase addition is commutative via spider fusion -/
theorem phase_add_comm (α β : Phase) : 
    compose (zPhase α) (zPhase β) ≃ compose (zPhase β) (zPhase α) := by
  have h1 := zSpider_fusion 1 1 α β
  have h2 := zSpider_fusion 1 1 β α
  rw [add_comm α β] at h1
  exact trans h1 (symm h2)

/-- Hadamard swaps Z and X -/
theorem hadamard_swap_colors (α : Phase) :
    compose hadamard (compose (zPhase α) hadamard) ≃ xPhase α := color_change_z α

/-- Double Hadamard is identity -/
theorem hadamard_squared : compose hadamard hadamard ≃ wire := hadamard_self_inverse

/-- Z[0] is identity -/
theorem z_phase_zero_id : zPhase 0 ≃ wire := zSpider_id

/-- X[0] is identity -/  
theorem x_phase_zero_id : xPhase 0 ≃ wire := xSpider_id

end ZXEquiv

end ZXClifford.ZX
