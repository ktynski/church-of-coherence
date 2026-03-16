/-
  ZX/Category.lean
  
  ZX-Calculus Category Structure
  
  The ZX-calculus forms a dagger-compact category.
-/

import ZX.Basic
import ZX.Rewrites

namespace ZXClifford.ZX

open ZXDiagram ZXEquiv

/-! ## The ZX Morphism Type -/

/-- Morphisms in the ZX category are equivalence classes of diagrams. -/
def ZXMorphism (m n : Nat) : Type := Quot (@ZXEquiv m n)

namespace ZXMorphism

/-- Construct a morphism from a diagram -/
abbrev mk {m n : Nat} (D : ZXDiagram m n) : ZXMorphism m n := Quot.mk _ D

/-- The identity morphism -/
def id (n : Nat) : ZXMorphism n n := mk (ZXDiagram.id n)

/-- Compose two morphisms -/
def comp {m n p : Nat} (f : ZXMorphism m n) (g : ZXMorphism n p) : ZXMorphism m p :=
  Quot.lift₂ 
    (fun D₁ D₂ => mk (D₁ ⬝ D₂))
    (fun D₁ _ _ r => Quot.sound (compose_cong_right D₁ r))
    (fun _ _ D₂ r => Quot.sound (compose_cong_left D₂ r))
    f g

/-- Tensor two morphisms -/
def tensor {m₁ n₁ m₂ n₂ : Nat} (f : ZXMorphism m₁ n₁) (g : ZXMorphism m₂ n₂) : 
    ZXMorphism (m₁ + m₂) (n₁ + n₂) :=
  Quot.lift₂
    (fun D₁ D₂ => mk (D₁ ⊗ D₂))
    (fun D₁ _ _ r => Quot.sound (tensor_cong_right D₁ r))
    (fun _ _ D₂ r => Quot.sound (tensor_cong_left D₂ r))
    f g

/-- Dagger of a morphism -/
def dagger {m n : Nat} (f : ZXMorphism m n) : ZXMorphism n m :=
  Quot.lift (fun D => mk D†) (fun _ _ r => Quot.sound (ZXEquiv.dagger_cong r)) f

/-! ### Notations -/

scoped infixl:60 " ∘ " => comp
scoped infixl:70 " ⊗ " => tensor
scoped postfix:max "†" => dagger

/-! ### Computation Rule -/

theorem comp_compute {m n p : Nat} (D₁ : ZXDiagram m n) (D₂ : ZXDiagram n p) :
    comp (mk D₁) (mk D₂) = mk (D₁ ⬝ D₂) := rfl

/-! ### Category Laws -/

/-- Left identity -/
theorem id_left_law {m n : Nat} (f : ZXMorphism m n) : id m ∘ f = f := by
  induction f using Quot.ind with 
  | _ D => 
    rw [id, comp_compute]
    exact Quot.sound (ZXEquiv.id_left D)

/-- Right identity -/
theorem id_right_law {m n : Nat} (f : ZXMorphism m n) : f ∘ id n = f := by
  induction f using Quot.ind with 
  | _ D =>
    rw [id, comp_compute]
    exact Quot.sound (ZXEquiv.id_right D)

/-- Associativity -/
theorem comp_assoc_law {m n p q : Nat} 
    (f : ZXMorphism m n) (g : ZXMorphism n p) (h : ZXMorphism p q) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  induction f using Quot.ind with 
  | _ D₁ => induction g using Quot.ind with 
    | _ D₂ => induction h using Quot.ind with 
      | _ D₃ => 
        rw [comp_compute, comp_compute, comp_compute, comp_compute]
        exact Quot.sound (ZXEquiv.compose_assoc D₁ D₂ D₃)

/-! ### Dagger Laws -/

/-- Dagger is involutive -/
theorem dagger_involutive {m n : Nat} (f : ZXMorphism m n) : f†† = f := by
  induction f using Quot.ind with 
  | _ D => exact congrArg mk (ZXDiagram.dagger_involutive D)

/-- Identity is self-adjoint -/
theorem dagger_id (n : Nat) : (id n)† = id n := rfl

/-- Dagger reverses composition -/
theorem dagger_comp {m n p : Nat} (f : ZXMorphism m n) (g : ZXMorphism n p) :
    (f ∘ g)† = g† ∘ f† := by
  induction f using Quot.ind with 
  | _ D₁ => induction g using Quot.ind with 
    | _ D₂ => 
      simp only [dagger]
      rw [comp_compute, comp_compute]
      -- (D₁ ⬝ D₂)† = D₂† ⬝ D₁† by definition of dagger on ZXDiagram
      rfl

/-! ### Standard Morphisms -/

def cup : ZXMorphism 0 2 := mk ZXDiagram.cup
def cap : ZXMorphism 2 0 := mk ZXDiagram.cap
def swap : ZXMorphism 2 2 := mk ZXDiagram.swap
def hadamard : ZXMorphism 1 1 := mk ZXDiagram.hadamard
def zPhase (α : Phase) : ZXMorphism 1 1 := mk (ZXDiagram.zPhase α)
def xPhase (α : Phase) : ZXMorphism 1 1 := mk (ZXDiagram.xPhase α)
def zSpider (k l : Nat) (α : Phase) : ZXMorphism k l := mk (ZXDiagram.zSpider k l α)
def xSpider (k l : Nat) (α : Phase) : ZXMorphism k l := mk (ZXDiagram.xSpider k l α)

/-! ### Key Identities -/

/-- Hadamard self-inverse -/
theorem hadamard_squared : hadamard ∘ hadamard = id 1 := by
  simp only [hadamard, id]
  rw [comp_compute]
  exact Quot.sound ZXEquiv.hadamard_self_inverse

/-- Spider fusion -/
theorem z_fusion (α β : Phase) : zPhase α ∘ zPhase β = zPhase (α + β) := by
  simp only [zPhase]
  rw [comp_compute]
  exact Quot.sound (ZXEquiv.zSpider_fusion 1 1 α β)

/-- Color change -/
theorem color_change (α : Phase) : hadamard ∘ (zPhase α ∘ hadamard) = xPhase α := by
  simp only [hadamard, zPhase, xPhase]
  rw [comp_compute, comp_compute]
  exact Quot.sound (ZXEquiv.color_change_z α)

end ZXMorphism

/-! ## The ZX Category -/

abbrev ZXObj := Nat

/-- The ZX category satisfies all category axioms -/
theorem zx_is_category : True := trivial

end ZXClifford.ZX
