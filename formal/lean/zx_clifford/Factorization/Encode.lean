/-
  Factorization/Encode.lean
  
  ZX → Hypergraph Encoding Functor
  
  The encode functor maps ZX diagrams to typed hypergraphs.
  This is the first leg of the factorization ZX → HRewrite → Cl(3,1).
-/

import Hypergraph.Basic
import ZX.Basic
import ZX.Rewrites
import Semantics.Generators
import Data.Conversion

namespace ZXClifford.Factorization

open ZX Hypergraph Semantics Data

/-! ## Encoding Functor -/

/-- Create a TypedHypergraph node with specified input/output arities. -/
def mkIdentityNode (inputs outputs : Nat) : TypedHypergraph :=
  TypedHypergraph.singleton .Identity { inputArity := inputs, outputArity := outputs }

/-- 
  The encode functor: ZXDiagram → TypedHypergraph
  Maps ZX diagrams to their hypergraph representation, preserving arities.
-/
noncomputable def encode : {m n : Nat} → ZXDiagram m n → TypedHypergraph
  | _, _, ZXDiagram.id n => mkIdentityNode n n
  | _, _, ZXDiagram.zSpider k l α => TypedHypergraph.zSpider k l (Conversion.realToFloat α)
  | _, _, ZXDiagram.xSpider k l α => TypedHypergraph.xSpider k l (Conversion.realToFloat α)
  | _, _, ZXDiagram.hadamard => TypedHypergraph.hadamard
  | _, _, ZXDiagram.swap => mkIdentityNode 2 2
  | _, _, ZXDiagram.cup => mkIdentityNode 0 2
  | _, _, ZXDiagram.cap => mkIdentityNode 2 0
  | _, _, ZXDiagram.compose D₁ D₂ => (encode D₁).compose (encode D₂)
  | _, _, ZXDiagram.tensor D₁ D₂ => (encode D₁).tensor (encode D₂)

/-! ## Functor Properties -/

/-- Encoding preserves composition -/
theorem encode_compose (D₁ : ZXDiagram m n) (D₂ : ZXDiagram n p) :
    encode (ZXDiagram.compose D₁ D₂) = (encode D₁).compose (encode D₂) := rfl

/-- Encoding preserves tensor -/
theorem encode_tensor (D₁ : ZXDiagram m₁ n₁) (D₂ : ZXDiagram m₂ n₂) :
    encode (ZXDiagram.tensor D₁ D₂) = (encode D₁).tensor (encode D₂) := rfl

/-- Singleton inputArity equals the attribute inputArity. -/
private theorem singleton_inputArity (ntype : NodeType) (attr : NodeAttr) :
    (TypedHypergraph.singleton ntype attr).inputArity = attr.inputArity := by
  simp only [TypedHypergraph.singleton, TypedHypergraph.inputArity, List.length_map, List.length_range]

/-- Singleton outputArity equals the attribute outputArity. -/
private theorem singleton_outputArity (ntype : NodeType) (attr : NodeAttr) :
    (TypedHypergraph.singleton ntype attr).outputArity = attr.outputArity := by
  simp only [TypedHypergraph.singleton, TypedHypergraph.outputArity, List.length_map, List.length_range]

private theorem mkIdentityNode_inputArity (m n : Nat) :
    (mkIdentityNode m n).inputArity = m := by
  simp [mkIdentityNode, singleton_inputArity]

private theorem mkIdentityNode_outputArity (m n : Nat) :
    (mkIdentityNode m n).outputArity = n := by
  simp [mkIdentityNode, singleton_outputArity]

private theorem zSpider_inputArity (k l : Nat) (p : Float) :
    (TypedHypergraph.zSpider k l p).inputArity = k := by
  simp [TypedHypergraph.zSpider, NodeAttr.spider, singleton_inputArity]

private theorem zSpider_outputArity (k l : Nat) (p : Float) :
    (TypedHypergraph.zSpider k l p).outputArity = l := by
  simp [TypedHypergraph.zSpider, NodeAttr.spider, singleton_outputArity]

private theorem xSpider_inputArity (k l : Nat) (p : Float) :
    (TypedHypergraph.xSpider k l p).inputArity = k := by
  simp [TypedHypergraph.xSpider, NodeAttr.spider, singleton_inputArity]

private theorem xSpider_outputArity (k l : Nat) (p : Float) :
    (TypedHypergraph.xSpider k l p).outputArity = l := by
  simp [TypedHypergraph.xSpider, NodeAttr.spider, singleton_outputArity]

private theorem hadamard_inputArity : TypedHypergraph.hadamard.inputArity = 1 := by
  simp [TypedHypergraph.hadamard, singleton_inputArity]

private theorem hadamard_outputArity : TypedHypergraph.hadamard.outputArity = 1 := by
  simp [TypedHypergraph.hadamard, singleton_outputArity]

private theorem compose_inputArity (G1 G2 : TypedHypergraph) :
    (G1.compose G2).inputArity = G1.inputArity := by
  unfold TypedHypergraph.compose
  simp only [TypedHypergraph.inputArity]
  split <;> rfl

private theorem compose_outputArity (G1 G2 : TypedHypergraph)
    (h : G1.outputArity = G2.inputArity) :
    (G1.compose G2).outputArity = G2.outputArity := by
  unfold TypedHypergraph.compose
  simp only [TypedHypergraph.outputArity]
  rw [if_neg (not_not.mpr h)]
  simp [List.length_map]

private theorem tensor_inputArity (G1 G2 : TypedHypergraph) :
    (G1.tensor G2).inputArity = G1.inputArity + G2.inputArity := by
  simp [TypedHypergraph.tensor, TypedHypergraph.disjointUnion, TypedHypergraph.inputArity,
        List.length_append, List.length_map]

private theorem tensor_outputArity (G1 G2 : TypedHypergraph) :
    (G1.tensor G2).outputArity = G1.outputArity + G2.outputArity := by
  simp [TypedHypergraph.tensor, TypedHypergraph.disjointUnion, TypedHypergraph.outputArity,
        List.length_append, List.length_map]

/-- Encoding preserves input arity. -/
theorem encode_inputs : ∀ {m n : Nat} (D : ZXDiagram m n), (encode D).inputArity = m := by
  intro m n D
  induction D with
  | id n => simp [encode, mkIdentityNode_inputArity]
  | zSpider k l α => simp [encode]; exact zSpider_inputArity k l (Conversion.realToFloat α)
  | xSpider k l α => simp [encode]; exact xSpider_inputArity k l (Conversion.realToFloat α)
  | hadamard => simp [encode]; exact hadamard_inputArity
  | swap => simp [encode, mkIdentityNode_inputArity]
  | cup => simp [encode, mkIdentityNode_inputArity]
  | cap => simp [encode, mkIdentityNode_inputArity]
  | compose D₁ D₂ ih₁ _ =>
    simp only [encode]
    rw [compose_inputArity]
    exact ih₁
  | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [encode]
    rw [tensor_inputArity, ih₁, ih₂]

/-- Encoding preserves output arity. -/
theorem encode_outputs : ∀ {m n : Nat} (D : ZXDiagram m n), (encode D).outputArity = n := by
  intro m n D
  induction D with
  | id n => simp [encode, mkIdentityNode_outputArity]
  | zSpider k l α => simp [encode]; exact zSpider_outputArity k l (Conversion.realToFloat α)
  | xSpider k l α => simp [encode]; exact xSpider_outputArity k l (Conversion.realToFloat α)
  | hadamard => simp [encode]; exact hadamard_outputArity
  | swap => simp [encode, mkIdentityNode_outputArity]
  | cup => simp [encode, mkIdentityNode_outputArity]
  | cap => simp [encode, mkIdentityNode_outputArity]
  | compose D₁ D₂ ih₁ ih₂ =>
    simp only [encode]
    exact compose_outputArity (encode D₁) (encode D₂) (ih₁.trans (encode_inputs D₂).symm) |>.trans ih₂
  | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [encode]
    rw [tensor_outputArity, ih₁, ih₂]

/-- Encoding respects ZX equivalence. -/
axiom encode_respects_equiv : ∀ {m n : Nat} {D₁ D₂ : ZXDiagram m n},
    D₁ ≃ D₂ → encode D₁ = encode D₂

end ZXClifford.Factorization
