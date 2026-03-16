/-
  Hypergraph/Basic.lean
  
  Typed Hypergraph Data Structures
  
  A hypergraph generalizes graphs by allowing edges to connect any number of nodes.
  This is the natural structure for representing ZX diagrams:
  - Nodes represent spiders (generators)
  - Hyperedges represent wire connections
  - Ports represent input/output interfaces
  
  Following Gorard's approach, we use typed hypergraphs where:
  - Nodes have types (Z, X, H, etc.)
  - Nodes have attributes (phase values)
  - Ports are typed (input vs output)
  
  Reference: "ZX-Calculus and Extended Hypergraph Rewriting Systems" (Gorard et al.)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace ZXClifford.Hypergraph

/-! ## Basic Types -/

/-- Unique identifier for nodes -/
abbrev NodeId := Nat

/-- Unique identifier for hyperedges -/
abbrev HyperedgeId := Nat

/-- Unique identifier for ports -/
abbrev PortId := Nat

/-! ## Node Types -/

/-- Types of nodes in a ZX hypergraph -/
inductive NodeType
  | ZSpider       -- Green spider (Z basis)
  | XSpider       -- Red spider (X basis)
  | Hadamard      -- Hadamard box
  | Identity      -- Identity/wire junction
  | Input         -- External input port
  | Output        -- External output port
deriving DecidableEq, Repr

namespace NodeType

/-- Is this a spider node? -/
def isSpider : NodeType → Bool
  | ZSpider => true
  | XSpider => true
  | _ => false

/-- Is this a boundary node (input/output)? -/
def isBoundary : NodeType → Bool
  | Input => true
  | Output => true
  | _ => false

/-- Swap spider colors -/
def swapColor : NodeType → NodeType
  | ZSpider => XSpider
  | XSpider => ZSpider
  | t => t

end NodeType

/-! ## Node Attributes -/

/-- Attributes associated with a node -/
structure NodeAttr where
  /-- Phase (for spiders) -/
  phase : Float := 0.0
  /-- Number of input connections -/
  inputArity : Nat := 0
  /-- Number of output connections -/
  outputArity : Nat := 0
  /-- Optional label -/
  label : Option String := none
deriving Repr

namespace NodeAttr

/-- Default attributes -/
def default : NodeAttr := {}

/-- Spider with given phase -/
def spider (α : Float) (inputs outputs : Nat) : NodeAttr := 
  { phase := α, inputArity := inputs, outputArity := outputs }

/-- Identity node -/
def identity : NodeAttr := { inputArity := 1, outputArity := 1 }

end NodeAttr

/-! ## Port Types -/

/-- Direction of a port -/
inductive PortDirection
  | In   -- Input port
  | Out  -- Output port
deriving DecidableEq, Repr

/-- A port is an interface point on a node -/
structure Port where
  /-- Which node this port belongs to -/
  node : NodeId
  /-- Which connection index on the node -/
  index : Nat
  /-- Input or output -/
  direction : PortDirection
deriving DecidableEq, Repr

/-! ## Hyperedge -/

/-- 
  A hyperedge connects multiple ports.
  For ZX diagrams, most edges are binary (connecting two ports),
  but the structure supports arbitrary hyperedges.
-/
structure Hyperedge where
  /-- Unique identifier -/
  id : HyperedgeId
  /-- List of connected ports -/
  ports : List Port
  /-- Edge label (optional) -/
  label : Option String := none
deriving Repr

namespace Hyperedge

/-- Arity of a hyperedge -/
def arity (e : Hyperedge) : Nat := e.ports.length

/-- Is this a binary edge (standard wire)? -/
def isBinary (e : Hyperedge) : Bool := e.arity == 2

/-- Get all nodes connected by this edge -/
def connectedNodes (e : Hyperedge) : List NodeId := 
  e.ports.map Port.node

end Hyperedge

/-! ## Typed Hypergraph -/

/-- 
  A typed hypergraph representing a ZX diagram or rewrite pattern.
  
  The structure tracks:
  - Nodes with types and attributes
  - Hyperedges connecting ports
  - External input/output interfaces
-/
structure TypedHypergraph where
  /-- Set of node identifiers -/
  nodes : List NodeId
  /-- Node type assignment -/
  nodeType : NodeId → NodeType
  /-- Node attributes -/
  nodeAttr : NodeId → NodeAttr
  /-- Set of hyperedges -/
  edges : List Hyperedge
  /-- External input ports (interface to outside) -/
  inPorts : List Port
  /-- External output ports -/
  outPorts : List Port
  /-- Next available node ID -/
  nextNodeId : NodeId := nodes.length
  /-- Next available edge ID -/
  nextEdgeId : HyperedgeId := edges.length

namespace TypedHypergraph

/-! ### Construction -/

/-- Empty hypergraph -/
def empty : TypedHypergraph := {
  nodes := []
  nodeType := fun _ => NodeType.Identity
  nodeAttr := fun _ => NodeAttr.default
  edges := []
  inPorts := []
  outPorts := []
}

/-- Single node hypergraph -/
def singleton (ntype : NodeType) (attr : NodeAttr) : TypedHypergraph := {
  nodes := [0]
  nodeType := fun _ => ntype
  nodeAttr := fun _ => attr
  edges := []
  inPorts := List.range attr.inputArity |>.map fun i => 
    { node := 0, index := i, direction := .In }
  outPorts := List.range attr.outputArity |>.map fun i => 
    { node := 0, index := i, direction := .Out }
}

/-- Z spider hypergraph -/
def zSpider (k l : Nat) (phase : Float) : TypedHypergraph :=
  singleton .ZSpider (NodeAttr.spider phase k l)

/-- X spider hypergraph -/
def xSpider (k l : Nat) (phase : Float) : TypedHypergraph :=
  singleton .XSpider (NodeAttr.spider phase k l)

/-- Hadamard hypergraph -/
def hadamard : TypedHypergraph :=
  singleton .Hadamard { inputArity := 1, outputArity := 1 }

/-- Identity wire -/
def wire : TypedHypergraph :=
  singleton .Identity NodeAttr.identity

/-! ### Queries -/

/-- Number of nodes -/
def nodeCount (G : TypedHypergraph) : Nat := G.nodes.length

/-- Number of edges -/
def edgeCount (G : TypedHypergraph) : Nat := G.edges.length

/-- Number of input ports -/
def inputArity (G : TypedHypergraph) : Nat := G.inPorts.length

/-- Number of output ports -/
def outputArity (G : TypedHypergraph) : Nat := G.outPorts.length

/-- Get all Z spider nodes -/
def zSpiders (G : TypedHypergraph) : List NodeId :=
  G.nodes.filter fun n => G.nodeType n == .ZSpider

/-- Get all X spider nodes -/
def xSpiders (G : TypedHypergraph) : List NodeId :=
  G.nodes.filter fun n => G.nodeType n == .XSpider

/-- Check if a node exists -/
def hasNode (G : TypedHypergraph) (n : NodeId) : Bool :=
  G.nodes.contains n

/-- Get edges connected to a node -/
def nodeEdges (G : TypedHypergraph) (n : NodeId) : List Hyperedge :=
  G.edges.filter fun e => e.connectedNodes.contains n

/-! ### Modification -/

/-- Add a node to the hypergraph -/
def addNode (G : TypedHypergraph) (ntype : NodeType) (attr : NodeAttr) : 
    TypedHypergraph × NodeId :=
  let newId := G.nextNodeId
  let G' := { G with
    nodes := G.nodes ++ [newId]
    nodeType := fun n => if n == newId then ntype else G.nodeType n
    nodeAttr := fun n => if n == newId then attr else G.nodeAttr n
    nextNodeId := newId + 1
  }
  (G', newId)

/-- Add an edge connecting ports -/
def addEdge (G : TypedHypergraph) (ports : List Port) : TypedHypergraph :=
  let newId := G.nextEdgeId
  let edge := { id := newId, ports := ports }
  { G with
    edges := G.edges ++ [edge]
    nextEdgeId := newId + 1
  }

/-- Connect two ports with a binary edge -/
def connect (G : TypedHypergraph) (p1 p2 : Port) : TypedHypergraph :=
  G.addEdge [p1, p2]

/-- Remove a node (and all connected edges) -/
def removeNode (G : TypedHypergraph) (n : NodeId) : TypedHypergraph :=
  { G with
    nodes := G.nodes.filter (· ≠ n)
    edges := G.edges.filter fun e => !e.connectedNodes.contains n
    inPorts := G.inPorts.filter fun p => p.node ≠ n
    outPorts := G.outPorts.filter fun p => p.node ≠ n
  }

/-! ### Composition Operations -/

/-- 
  Disjoint union of two hypergraphs.
  Node IDs in the second graph are shifted to avoid collision.
-/
def disjointUnion (G1 G2 : TypedHypergraph) : TypedHypergraph :=
  let shift := G1.nextNodeId
  let shiftedNodes := G2.nodes.map (· + shift)
  let shiftPort (p : Port) : Port := { p with node := p.node + shift }
  let shiftEdge (e : Hyperedge) : Hyperedge := 
    { e with 
      id := e.id + G1.nextEdgeId
      ports := e.ports.map shiftPort }
  { nodes := G1.nodes ++ shiftedNodes
    nodeType := fun n => 
      if n < shift then G1.nodeType n 
      else G2.nodeType (n - shift)
    nodeAttr := fun n =>
      if n < shift then G1.nodeAttr n
      else G2.nodeAttr (n - shift)
    edges := G1.edges ++ G2.edges.map shiftEdge
    inPorts := G1.inPorts ++ G2.inPorts.map shiftPort
    outPorts := G1.outPorts ++ G2.outPorts.map shiftPort
    nextNodeId := G1.nextNodeId + G2.nodeCount
    nextEdgeId := G1.nextEdgeId + G2.edgeCount
  }

/-- Tensor product (side-by-side) -/
def tensor (G1 G2 : TypedHypergraph) : TypedHypergraph :=
  disjointUnion G1 G2

/-- 
  Sequential composition: connect G1's outputs to G2's inputs.
  Requires G1.outputArity = G2.inputArity
-/
def compose (G1 G2 : TypedHypergraph) : TypedHypergraph :=
  if G1.outputArity ≠ G2.inputArity then G1  -- Error case
  else
    let combined := disjointUnion G1 G2
    -- Connect matching output-input pairs
    let shift := G1.nextNodeId
    let connections := List.zip G1.outPorts (G2.inPorts.map fun p => { p with node := p.node + shift })
    let withEdges := connections.foldl 
      (fun G (p1, p2) => G.connect p1 p2) 
      combined
    -- Update external ports: inputs from G1, outputs from G2
    { withEdges with
      inPorts := G1.inPorts
      outPorts := G2.outPorts.map fun p => { p with node := p.node + shift }
    }

/-! ### Notations -/

scoped infixl:60 " ⬝ " => compose
scoped infixl:70 " ⊗ " => tensor

end TypedHypergraph

/-! ## Graph Morphisms -/

/-- 
  A morphism between hypergraphs maps nodes to nodes and edges to edges,
  preserving types and connectivity.
-/
structure HypergraphMorphism (G H : TypedHypergraph) where
  /-- Node mapping -/
  nodeMap : NodeId → NodeId
  /-- Edge mapping -/
  edgeMap : HyperedgeId → HyperedgeId
  /-- Type preservation -/
  typePreserving : ∀ n, G.hasNode n → H.nodeType (nodeMap n) = G.nodeType n
  /-- Node membership preservation -/
  membershipPreserving : ∀ n, G.hasNode n → H.hasNode (nodeMap n)
  /-- Connectivity preservation -/
  connectivityPreserving : True  -- Simplified

namespace HypergraphMorphism

/-- Identity morphism -/
def id (G : TypedHypergraph) : HypergraphMorphism G G := {
  nodeMap := fun n => n
  edgeMap := fun e => e
  typePreserving := fun _ _ => rfl
  membershipPreserving := fun _ hn => hn
  connectivityPreserving := trivial
}

/-- Morphisms preserve node membership (now a theorem from the structure field). -/
theorem morphism_preserves_membership {G H : TypedHypergraph}
    (f : HypergraphMorphism G H) (n : NodeId) (hn : G.hasNode n) :
    H.hasNode (f.nodeMap n) :=
  f.membershipPreserving n hn

/-- Composition of morphisms -/
def comp {G H K : TypedHypergraph}
    (f : HypergraphMorphism G H) (g : HypergraphMorphism H K) :
    HypergraphMorphism G K := {
  nodeMap := g.nodeMap ∘ f.nodeMap
  edgeMap := g.edgeMap ∘ f.edgeMap
  typePreserving := fun n hn => by
    simp only [Function.comp_apply]
    have hf := f.typePreserving n hn
    have hfn := f.membershipPreserving n hn
    have hg := g.typePreserving (f.nodeMap n) hfn
    rw [hg, hf]
  membershipPreserving := fun n hn => by
    simp only [Function.comp_apply]
    exact g.membershipPreserving _ (f.membershipPreserving n hn)
  connectivityPreserving := trivial
}

end HypergraphMorphism

/-! ## Subgraph and Matching -/

/-- A match is an embedding of a pattern into a host graph -/
structure Match (pattern host : TypedHypergraph) where
  /-- The embedding morphism -/
  morphism : HypergraphMorphism pattern host
  /-- Injectivity on nodes -/
  injective : True  -- Simplified

/-- Find all matches of a pattern in a host graph -/
def findMatches (pattern host : TypedHypergraph) : List (Match pattern host) :=
  []  -- Placeholder: actual implementation requires graph matching algorithm

end ZXClifford.Hypergraph
