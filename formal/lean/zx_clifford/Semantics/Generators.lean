/-
  Semantics/Generators.lean

  ZX Generator Semantics in Clifford Algebra

  Each ZX generator maps to a specific Clifford algebra operator:
  - Z spiders → Phase rotations in the e₁-e₂ plane
  - X spiders → Phase rotations in the e₂-e₃ plane
  - Hadamard → (e₁ + e₃)/√2 acting by left multiplication
  - Cup/Cap → Bell pair operations

  This mapping is the core of the ZX→Clifford semantics functor.

  SORRY STATUS: 0 sorry (all 3 former sorry-theorems now proved)
  AXIOM STATUS: 0 axioms

  Reference: Categorical semantics of ZX-calculus
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ZX.Basic

namespace ZXClifford.Semantics

open ZX

/-! ## Clifford Algebra Cl(3,1) — Explicit 16-component representation over ℝ -/

/--
  Explicit representation of Cl(3,1) elements over ℝ.
  16-dimensional with grades 0-4.

  Basis ordering:
    grade 0: scalar (1 component)
    grade 1: vector[0..3] = (e₁, e₂, e₃, e₄)
    grade 2: bivector[0..5] = (e₁₂, e₁₃, e₁₄, e₂₃, e₂₄, e₃₄)
    grade 3: trivector[0..3] = (e₁₂₃, e₁₂₄, e₁₃₄, e₂₃₄)
    grade 4: pseudoscalar (e₁₂₃₄)
-/
structure Cl31 where
  scalar : ℝ
  vector : Fin 4 → ℝ
  bivector : Fin 6 → ℝ
  trivector : Fin 4 → ℝ
  pseudoscalar : ℝ

namespace Cl31

/-! ### Extensionality -/

@[ext]
theorem ext (u v : Cl31)
    (hs : u.scalar = v.scalar)
    (hv : u.vector = v.vector)
    (hb : u.bivector = v.bivector)
    (ht : u.trivector = v.trivector)
    (hp : u.pseudoscalar = v.pseudoscalar) : u = v := by
  cases u; cases v; simp_all

/-! ### Basic Operations -/

noncomputable def zero : Cl31 :=
  ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, 0⟩

noncomputable def one : Cl31 :=
  ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, 0⟩

noncomputable def add (u v : Cl31) : Cl31 :=
  ⟨u.scalar + v.scalar,
   fun i => u.vector i + v.vector i,
   fun i => u.bivector i + v.bivector i,
   fun i => u.trivector i + v.trivector i,
   u.pseudoscalar + v.pseudoscalar⟩

noncomputable def neg (u : Cl31) : Cl31 :=
  ⟨-u.scalar, fun i => -u.vector i, fun i => -u.bivector i,
   fun i => -u.trivector i, -u.pseudoscalar⟩

noncomputable def smul (c : ℝ) (u : Cl31) : Cl31 :=
  ⟨c * u.scalar, fun i => c * u.vector i, fun i => c * u.bivector i,
   fun i => c * u.trivector i, c * u.pseudoscalar⟩

noncomputable instance : Zero Cl31 := ⟨zero⟩
noncomputable instance : One Cl31 := ⟨one⟩
noncomputable instance : Add Cl31 := ⟨add⟩
noncomputable instance : Neg Cl31 := ⟨neg⟩
noncomputable instance : HMul ℝ Cl31 Cl31 := ⟨smul⟩

/-! ### Basis Elements -/

noncomputable def e1 : Cl31 := { zero with vector := fun i => if i == 0 then 1 else 0 }
noncomputable def e2 : Cl31 := { zero with vector := fun i => if i == 1 then 1 else 0 }
noncomputable def e3 : Cl31 := { zero with vector := fun i => if i == 2 then 1 else 0 }
noncomputable def e4 : Cl31 := { zero with vector := fun i => if i == 3 then 1 else 0 }
noncomputable def e12 : Cl31 := { zero with bivector := fun i => if i == 0 then 1 else 0 }
noncomputable def e23 : Cl31 := { zero with bivector := fun i => if i == 3 then 1 else 0 }
noncomputable def e13 : Cl31 := { zero with bivector := fun i => if i == 1 then 1 else 0 }

/-! ### Full Clifford Product

The complete bilinear Clifford product for Cl(3,1) with signature (+,+,+,-).
Each output component is a sum of products of input components with signs
determined by the Clifford product table (verified against the 4×4 gamma-matrix
representation in test_zx_axiom_witnesses.py: TestFullProduct).
-/

noncomputable def mul (u v : Cl31) : Cl31 :=
  let s := u.scalar
  let v0 := u.vector 0; let v1 := u.vector 1
  let v2 := u.vector 2; let v3 := u.vector 3
  let b0 := u.bivector 0; let b1 := u.bivector 1; let b2 := u.bivector 2
  let b3 := u.bivector 3; let b4 := u.bivector 4; let b5 := u.bivector 5
  let t0 := u.trivector 0; let t1 := u.trivector 1
  let t2 := u.trivector 2; let t3 := u.trivector 3
  let p := u.pseudoscalar
  let s' := v.scalar
  let v0' := v.vector 0; let v1' := v.vector 1
  let v2' := v.vector 2; let v3' := v.vector 3
  let b0' := v.bivector 0; let b1' := v.bivector 1; let b2' := v.bivector 2
  let b3' := v.bivector 3; let b4' := v.bivector 4; let b5' := v.bivector 5
  let t0' := v.trivector 0; let t1' := v.trivector 1
  let t2' := v.trivector 2; let t3' := v.trivector 3
  let p' := v.pseudoscalar
  ⟨
    -- scalar
    s*s' + v0*v0' + v1*v1' + v2*v2' - v3*v3'
    - b0*b0' - b1*b1' + b2*b2' - b3*b3' + b4*b4' + b5*b5'
    - t0*t0' + t1*t1' + t2*t2' + t3*t3' - p*p',

    -- vector
    fun i => match i with
    | 0 => s*v0' + v0*s' - v1*b0' - v2*b1' + v3*b2'
          + b0*v1' + b1*v2' - b2*v3'
          - b3*t0' + b4*t1' + b5*t2'
          - t0*b3' + t1*b4' + t2*b5' - t3*p' + p*t3'
    | 1 => s*v1' + v0*b0' + v1*s' - v2*b3' + v3*b4'
          - b0*v0' + b1*t0' - b2*t1'
          + b3*v2' - b4*v3' + b5*t3'
          + t0*b1' - t1*b2' + t2*p' + t3*b5' - p*t2'
    | 2 => s*v2' + v0*b1' + v1*b3' + v2*s' + v3*b5'
          - b0*t0' - b1*v0' - b2*t2'
          - b3*v1' - b4*t3' - b5*v3'
          - t0*b0' - t1*p' - t2*b2' - t3*b4' + p*t1'
    | 3 => s*v3' + v0*b2' + v1*b4' + v2*b5' + v3*s'
          - b0*t1' - b1*t2' - b2*v0'
          - b3*t3' - b4*v1' - b5*v2'
          - t0*p' - t1*b0' - t2*b1' - t3*b3' + p*t0',

    -- bivector
    fun i => match i with
    | 0 => s*b0' + v0*v1' - v1*v0' + v2*t0' - v3*t1'
          + b0*s' - b1*b3' + b2*b4'
          + b3*b1' - b4*b2' + b5*p'
          + t0*v2' - t1*v3' + t2*t3' - t3*t2' + p*b5'
    | 1 => s*b1' + v0*v2' - v1*t0' - v2*v0' - v3*t2'
          + b0*b3' + b1*s' + b2*b5'
          - b3*b0' - b4*p' - b5*b2'
          - t0*v1' - t1*t3' - t2*v3' + t3*t1' - p*b4'
    | 2 => s*b2' + v0*v3' - v1*t1' - v2*t2' - v3*v0'
          + b0*b4' + b1*b5' + b2*s'
          - b3*p' - b4*b0' - b5*b1'
          - t0*t3' - t1*v1' - t2*v2' + t3*t0' - p*b3'
    | 3 => s*b3' + v0*t0' + v1*v2' - v2*v1' - v3*t3'
          - b0*b1' + b1*b0' + b2*p'
          + b3*s' + b4*b5' - b5*b4'
          + t0*v0' + t1*t2' - t2*t1' - t3*v3' + p*b2'
    | 4 => s*b4' + v0*t1' + v1*v3' - v2*t3' - v3*v1'
          - b0*b2' + b1*p' + b2*b0'
          + b3*b5' + b4*s' - b5*b3'
          + t0*t2' + t1*v0' - t2*t0' - t3*v2' + p*b1'
    | 5 => s*b5' + v0*t2' + v1*t3' + v2*v3' - v3*v2'
          - b0*p' - b1*b2' + b2*b1'
          - b3*b4' + b4*b3' + b5*s'
          - t0*t1' + t1*t0' + t2*v0' + t3*v1' - p*b0',

    -- trivector
    fun i => match i with
    | 0 => s*t0' + v0*b3' - v1*b1' + v2*b0' + v3*p'
          + b0*v2' - b1*v1' - b2*t3'
          + b3*v0' + b4*t2' - b5*t1'
          + t0*s' + t1*b5' - t2*b4' + t3*b2' - p*v3'
    | 1 => s*t1' + v0*b4' - v1*b2' + v2*p' + v3*b0'
          + b0*v3' - b1*t3' - b2*v1'
          + b3*t2' + b4*v0' - b5*t0'
          + t0*b5' + t1*s' - t2*b3' + t3*b1' - p*v2'
    | 2 => s*t2' + v0*b5' - v1*p' - v2*b2' + v3*b1'
          + b0*t3' + b1*v3' - b2*v2'
          - b3*t1' + b4*t0' + b5*v0'
          - t0*b4' + t1*b3' + t2*s' - t3*b0' + p*v1'
    | 3 => s*t3' + v0*p' + v1*b5' - v2*b4' + v3*b3'
          - b0*t2' + b1*t1' - b2*t0'
          + b3*v3' - b4*v2' + b5*v1'
          + t0*b2' - t1*b1' + t2*b0' + t3*s' - p*v0',

    -- pseudoscalar
    s*p' + v0*t3' - v1*t2' + v2*t1' - v3*t0'
    + b0*b5' - b1*b4' + b2*b3'
    + b3*b2' - b4*b1' + b5*b0'
    + t0*v3' - t1*v2' + t2*v1' - t3*v0' + p*s'
  ⟩

noncomputable instance : Mul Cl31 := ⟨mul⟩

/-! ### Exponential of Bivector -/

noncomputable def expBivector (θ : ℝ) (B : Cl31) : Cl31 :=
  add (smul (Real.cos θ) one) (smul (Real.sin θ) B)

noncomputable def rotorE12 (θ : ℝ) : Cl31 := expBivector (θ / 2) e12
noncomputable def rotorE23 (θ : ℝ) : Cl31 := expBivector (θ / 2) e23

/-! ### Grace Operator -/

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def grace (u : Cl31) : Cl31 :=
  ⟨u.scalar,
   fun i => u.vector i / φ,
   fun i => u.bivector i / (φ * φ),
   fun i => u.trivector i / (φ * φ * φ),
   u.pseudoscalar / (φ * φ * φ * φ)⟩

noncomputable def graceNormSq (u : Cl31) : ℝ :=
  u.scalar * u.scalar +
  (u.vector 0 ^ 2 + u.vector 1 ^ 2 + u.vector 2 ^ 2 + u.vector 3 ^ 2) / φ +
  (u.bivector 0 ^ 2 + u.bivector 1 ^ 2 + u.bivector 2 ^ 2 +
   u.bivector 3 ^ 2 + u.bivector 4 ^ 2 + u.bivector 5 ^ 2) / (φ * φ) +
  (u.trivector 0 ^ 2 + u.trivector 1 ^ 2 + u.trivector 2 ^ 2 + u.trivector 3 ^ 2) / (φ * φ * φ) +
  u.pseudoscalar * u.pseudoscalar / (φ * φ * φ * φ)

noncomputable def graceInner (u v : Cl31) : ℝ :=
  u.scalar * v.scalar +
  (u.vector 0 * v.vector 0 + u.vector 1 * v.vector 1 +
   u.vector 2 * v.vector 2 + u.vector 3 * v.vector 3) / φ +
  (u.bivector 0 * v.bivector 0 + u.bivector 1 * v.bivector 1 + u.bivector 2 * v.bivector 2 +
   u.bivector 3 * v.bivector 3 + u.bivector 4 * v.bivector 4 + u.bivector 5 * v.bivector 5) / (φ * φ) +
  (u.trivector 0 * v.trivector 0 + u.trivector 1 * v.trivector 1 +
   u.trivector 2 * v.trivector 2 + u.trivector 3 * v.trivector 3) / (φ * φ * φ) +
  u.pseudoscalar * v.pseudoscalar / (φ * φ * φ * φ)

end Cl31

/-! ## Qubit State Space -/

def QubitSpace : Nat → Type
  | 0 => Unit
  | 1 => Cl31
  | n + 2 => Cl31 × QubitSpace (n + 1)

@[ext] theorem qubitSpace1_ext (a b : QubitSpace 1)
    (hs : (a : Cl31).scalar = (b : Cl31).scalar)
    (hv : (a : Cl31).vector = (b : Cl31).vector)
    (hb : (a : Cl31).bivector = (b : Cl31).bivector)
    (ht : (a : Cl31).trivector = (b : Cl31).trivector)
    (hp : (a : Cl31).pseudoscalar = (b : Cl31).pseudoscalar) : a = b :=
  Cl31.ext a b hs hv hb ht hp

/-! ## Generator Semantics -/

namespace GeneratorSemantics

/-! ### Copy helper: replicate a Cl31 value to fill a QubitSpace -/

noncomputable def copyToQubitSpace (n : Nat) (x : Cl31) : QubitSpace n :=
  match n with
  | 0 => ()
  | 1 => x
  | n + 2 => (x, copyToQubitSpace (n + 1) x)

/-! ### Contract helper: fold Clifford product across all qubits in a QubitSpace -/

noncomputable def contractInputs : (n : Nat) → QubitSpace n → Cl31
  | 0, _ => Cl31.one
  | 1, x => x
  | n + 2, (x, rest) => Cl31.mul x (contractInputs (n + 1) rest)

/-! ### Z Spider Semantics -/

noncomputable def zSpider_1_1 (α : ℝ) : Cl31 → Cl31 :=
  fun state => Cl31.mul (Cl31.rotorE12 α) state

noncomputable def zSpider_0_n (n : Nat) (α : ℝ) : Unit → QubitSpace n :=
  fun _ => match n with
  | 0 => ()
  | 1 => Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                   (Cl31.smul (Real.sin (α/2)) Cl31.e12)
  | n + 2 =>
      let singleQubit := Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                                   (Cl31.smul (Real.sin (α/2)) Cl31.e12)
      (singleQubit, zSpider_0_n (n + 1) α ())

noncomputable def zSpider_n_0 (n : Nat) (_ : ℝ) : QubitSpace n → Unit :=
  fun _ => ()

noncomputable def zSpider_k_l (k l : Nat) (α : ℝ) : QubitSpace k → QubitSpace l :=
  match k, l with
  | 0, 0 => fun _ => ()
  | 0, l => zSpider_0_n l α
  | k, 0 => zSpider_n_0 k α
  | 1, 1 => zSpider_1_1 α
  | 1, l + 2 => fun x =>
      let out1 := zSpider_1_1 α x
      (out1, copyToQubitSpace (l + 1) out1)
  | k + 2, 1 => fun input =>
      zSpider_1_1 α (contractInputs (k + 2) input)
  | k + 2, l + 2 => fun input =>
      let processed := zSpider_1_1 α (contractInputs (k + 2) input)
      (processed, copyToQubitSpace (l + 1) processed)

/-! ### X Spider Semantics -/

noncomputable def xSpider_1_1 (α : ℝ) : Cl31 → Cl31 :=
  fun state => Cl31.mul (Cl31.rotorE23 α) state

noncomputable def xSpider_0_n (n : Nat) (α : ℝ) : Unit → QubitSpace n :=
  fun _ => match n with
  | 0 => ()
  | 1 => Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                   (Cl31.smul (Real.sin (α/2)) Cl31.e23)
  | n + 2 =>
      let singleQubit := Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                                   (Cl31.smul (Real.sin (α/2)) Cl31.e23)
      (singleQubit, xSpider_0_n (n + 1) α ())

noncomputable def xSpider_k_l (k l : Nat) (α : ℝ) : QubitSpace k → QubitSpace l :=
  match k, l with
  | 0, 0 => fun _ => ()
  | 0, l => xSpider_0_n l α
  | k, 0 => fun _ => ()
  | 1, 1 => xSpider_1_1 α
  | 1, l + 2 => fun x =>
      let out1 := xSpider_1_1 α x
      (out1, copyToQubitSpace (l + 1) out1)
  | k + 2, 1 => fun input =>
      xSpider_1_1 α (contractInputs (k + 2) input)
  | k + 2, l + 2 => fun input =>
      let processed := xSpider_1_1 α (contractInputs (k + 2) input)
      (processed, copyToQubitSpace (l + 1) processed)

/-! ### Hadamard Semantics -/

noncomputable def hadamard : Cl31 → Cl31 :=
  let H := Cl31.add (Cl31.smul (1 / Real.sqrt 2) Cl31.e1)
                     (Cl31.smul (1 / Real.sqrt 2) Cl31.e3)
  fun state => Cl31.mul H state

/-! ### Swap, Cup, Cap, Identity -/

def swap : QubitSpace 2 → QubitSpace 2 :=
  fun (a, b) => (b, a)

noncomputable def cup : Unit → QubitSpace 2 :=
  fun _ => (Cl31.one, Cl31.one)

def cap : QubitSpace 2 → Unit :=
  fun _ => ()

def identity (n : Nat) : QubitSpace n → QubitSpace n :=
  fun x => x

end GeneratorSemantics

/-! ## Phase Conversion -/

noncomputable def phaseToFloat : ZX.Phase → ℝ := id

noncomputable def generatorSemantics : ZXGenerator → (Σ k l, QubitSpace k → QubitSpace l)
  | .zSpider k l α => ⟨k, l, GeneratorSemantics.zSpider_k_l k l (phaseToFloat α)⟩
  | .xSpider k l α => ⟨k, l, GeneratorSemantics.xSpider_k_l k l (phaseToFloat α)⟩
  | .hadamard => ⟨1, 1, GeneratorSemantics.hadamard⟩
  | .swap => ⟨2, 2, GeneratorSemantics.swap⟩
  | .cup => ⟨0, 2, GeneratorSemantics.cup⟩
  | .cap => ⟨2, 0, GeneratorSemantics.cap⟩

/-! ## Semantic Preservation Theorems -/

/-!
  ### Key lemma: mul of rotorE12 with rotorE12 gives angle addition.

  rotorE12(α) = cos(α/2) + sin(α/2)*e₁₂

  When we multiply two e₁₂-plane rotors, only the scalar and bivector[0]
  components interact (all other components are zero).

  The product's scalar = cos(α/2)*cos(β/2) - sin(α/2)*sin(β/2) = cos((α+β)/2)
  The product's bivector[0] = cos(α/2)*sin(β/2) + sin(α/2)*cos(β/2) = sin((α+β)/2)
-/

theorem rotorE12_mul (α β : ℝ) :
    Cl31.mul (Cl31.rotorE12 α) (Cl31.rotorE12 β) = Cl31.rotorE12 (α + β) := by
  simp only [Cl31.rotorE12, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
             Cl31.one, Cl31.e12, Cl31.zero]
  have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
  have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
      Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
  have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
      Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
  ext <;> simp <;> (try split) <;> (try simp) <;>
    (first | linarith [h_cos] | linarith [h_sin] | ring)

theorem rotorE23_mul (α β : ℝ) :
    Cl31.mul (Cl31.rotorE23 α) (Cl31.rotorE23 β) = Cl31.rotorE23 (α + β) := by
  simp only [Cl31.rotorE23, Cl31.expBivector, Cl31.mul, Cl31.add, Cl31.smul,
             Cl31.one, Cl31.e23, Cl31.zero]
  have h_split : (α + β) / 2 = α / 2 + β / 2 := by ring
  have h_cos : Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) =
      Real.cos ((α + β) / 2) := by rw [h_split, Real.cos_add]
  have h_sin : Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) =
      Real.sin ((α + β) / 2) := by rw [h_split, Real.sin_add]
  ext <;> simp <;> (try split) <;> (try simp) <;>
    (first | linarith [h_cos] | linarith [h_sin] | ring)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6400000 in
theorem mul_assoc_cl31 (a b c : Cl31) :
    Cl31.mul a (Cl31.mul b c) = Cl31.mul (Cl31.mul a b) c := by
  simp only [Cl31.mul]
  ext <;> simp <;> (try split) <;> ring

/-- Rotor composition: exp(α/2 · B) · exp(β/2 · B) · x = exp((α+β)/2 · B) · x -/
theorem rotor_composition_ax (α β : ℝ) (x : Cl31) :
    Cl31.mul (Cl31.rotorE12 α) (Cl31.mul (Cl31.rotorE12 β) x) =
    Cl31.mul (Cl31.rotorE12 (α + β)) x := by
  rw [mul_assoc_cl31, rotorE12_mul]

theorem rotorE23_composition_ax (α β : ℝ) (x : Cl31) :
    Cl31.mul (Cl31.rotorE23 α) (Cl31.mul (Cl31.rotorE23 β) x) =
    Cl31.mul (Cl31.rotorE23 (α + β)) x := by
  rw [mul_assoc_cl31, rotorE23_mul]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- Hadamard squared is identity: H(H(x)) = x -/
theorem hadamard_squared_ax (x : Cl31) :
    GeneratorSemantics.hadamard (GeneratorSemantics.hadamard x) = x := by
  simp only [GeneratorSemantics.hadamard]
  simp only [Cl31.mul, Cl31.add, Cl31.smul, Cl31.e1, Cl31.e3, Cl31.zero]
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsq2' : Real.sqrt 2 ^ 2 = 2 := by rw [sq]; exact hsq2
  ext <;> simp <;> (try split) <;> (try simp) <;> (try field_simp) <;>
    (try rw [hsq2'] at *) <;> (try linarith)

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
/-- Color change: H · Z[α] · H = X[α] -/
theorem color_change_ax (α : ℝ) (x : Cl31) :
    GeneratorSemantics.hadamard
      (GeneratorSemantics.zSpider_1_1 α
        (GeneratorSemantics.hadamard x)) =
    GeneratorSemantics.xSpider_1_1 α x := by
  simp only [GeneratorSemantics.hadamard, GeneratorSemantics.zSpider_1_1,
             GeneratorSemantics.xSpider_1_1]
  simp only [Cl31.mul, Cl31.add, Cl31.smul, Cl31.rotorE12, Cl31.rotorE23,
             Cl31.expBivector, Cl31.one, Cl31.e1, Cl31.e3, Cl31.e12, Cl31.e23, Cl31.zero]
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsq2' : Real.sqrt 2 ^ 2 = 2 := by rw [sq]; exact hsq2
  ext <;> simp <;> (try split) <;> (try simp) <;> (try field_simp) <;>
    (try rw [hsq2'] at *) <;> (try linarith)

/-! ### Derived Theorems -/

theorem z_phase_compose (α β : ℝ) :
    ∀ x, GeneratorSemantics.zSpider_1_1 α (GeneratorSemantics.zSpider_1_1 β x) =
         GeneratorSemantics.zSpider_1_1 (α + β) x := by
  intro x
  simp only [GeneratorSemantics.zSpider_1_1]
  exact rotor_composition_ax α β x

theorem hadamard_squared :
    ∀ x, GeneratorSemantics.hadamard (GeneratorSemantics.hadamard x) = x := by
  intro x
  exact hadamard_squared_ax x

theorem color_change (α : ℝ) :
    ∀ x, GeneratorSemantics.hadamard
           (GeneratorSemantics.zSpider_1_1 α
             (GeneratorSemantics.hadamard x)) =
         GeneratorSemantics.xSpider_1_1 α x := by
  intro x
  exact color_change_ax α x

/-! ### Copy-to-QubitSpace equals spider-0-n -/

theorem copyToQubitSpace_eq_zSpider_0_n (n : Nat) (α : ℝ) :
    GeneratorSemantics.copyToQubitSpace n
      (Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                (Cl31.smul (Real.sin (α/2)) Cl31.e12)) =
    GeneratorSemantics.zSpider_0_n n α () := by
  induction n with
  | zero => rfl
  | succ n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      simp only [GeneratorSemantics.copyToQubitSpace, GeneratorSemantics.zSpider_0_n]
      exact congr_arg _ ih

theorem copyToQubitSpace_eq_xSpider_0_n (n : Nat) (α : ℝ) :
    GeneratorSemantics.copyToQubitSpace n
      (Cl31.add (Cl31.smul (Real.cos (α/2)) Cl31.one)
                (Cl31.smul (Real.sin (α/2)) Cl31.e23)) =
    GeneratorSemantics.xSpider_0_n n α () := by
  induction n with
  | zero => rfl
  | succ n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      simp only [GeneratorSemantics.copyToQubitSpace, GeneratorSemantics.xSpider_0_n]
      exact congr_arg _ ih

/-! ### ContractInputs lemmas -/

private theorem mul_one_left' (x : Cl31) : Cl31.mul Cl31.one x = x := by
  simp only [Cl31.mul, Cl31.one]
  ext <;> simp <;> (try split) <;> (try simp) <;> ring

theorem contractInputs_two_one_left (x : Cl31) :
    GeneratorSemantics.contractInputs 2 (Cl31.one, x) = x := by
  simp only [GeneratorSemantics.contractInputs]
  exact mul_one_left' x

/-! ## Spinor-Module Semantics (Phase 2B)

The spinor module is the standard representation of Cl(3,1) on ℝ⁴ (or ℂ⁴).
For ZX-calculus Frobenius structure, we work on the computational basis
where copy = diagonal embedding and merge = diagonal projection.

This makes the Hopf law provable: copy ; swap ; merge = identity.
-/

namespace SpinorModule

/-! ### Spinor types

The spinor module provides the correct state space for the ZX-calculus Frobenius
structure. A single qubit is ℝ² (Spinor1), two qubits are ℝ⁴ (Spinor2), and
the 0-wire space is ℝ (carrying scalar/trace information needed for Hopf).

Convention: X(k,l,α) = H^⊗l · Z(k,l,α) · H^⊗k with unnormalized H = [[1,1],[1,−1]].
-/

structure Spinor1 where
  c0 : ℝ
  c1 : ℝ

@[ext] theorem Spinor1.ext (a b : Spinor1) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

structure Spinor2 where
  c00 : ℝ
  c01 : ℝ
  c10 : ℝ
  c11 : ℝ

@[ext] theorem Spinor2.ext (a b : Spinor2) (h00 : a.c00 = b.c00) (h01 : a.c01 = b.c01)
    (h10 : a.c10 = b.c10) (h11 : a.c11 = b.c11) : a = b := by
  cases a; cases b; simp_all

/-! ### Z-basis Frobenius algebra -/

noncomputable def zCopy (ψ : Spinor1) : Spinor2 :=
  ⟨ψ.c0, 0, 0, ψ.c1⟩

noncomputable def zMerge (ψ : Spinor2) : Spinor1 :=
  ⟨ψ.c00, ψ.c11⟩

noncomputable def zCreate (r : ℝ) : Spinor1 := ⟨r, r⟩

noncomputable def zDelete (ψ : Spinor1) : ℝ := ψ.c0 + ψ.c1

/-! ### X-basis Frobenius algebra

With H = [[1,1],[1,−1]]:
  X-merge = H · Z-merge · (H⊗H)     = [[2,0,0,2],[0,2,2,0]]
  X-copy  = (H⊗H) · Z-copy · H      = [[2,0],[0,2],[0,2],[2,0]]
  X-create = H · Z-create             gives (2r, 0)
  X-delete = Z-delete · H             gives 2·c0
-/

noncomputable def xMerge (ψ : Spinor2) : Spinor1 :=
  ⟨2 * ψ.c00 + 2 * ψ.c11, 2 * ψ.c01 + 2 * ψ.c10⟩

noncomputable def xCopy (ψ : Spinor1) : Spinor2 :=
  ⟨2 * ψ.c0, 2 * ψ.c1, 2 * ψ.c1, 2 * ψ.c0⟩

noncomputable def xCreate (r : ℝ) : Spinor1 := ⟨2 * r, 0⟩

noncomputable def xDelete (ψ : Spinor1) : ℝ := 2 * ψ.c0

def spinorSwap (ψ : Spinor2) : Spinor2 :=
  ⟨ψ.c00, ψ.c10, ψ.c01, ψ.c11⟩

/-! ### Hopf law (exact equality, no scalar gap)

Standard Hopf: Z-copy ; swap ; X-merge = Z-delete ; X-create.

LHS: (a, b) → (a,0,0,b) → swap → (a,0,0,b) → xMerge → (2a+2b, 0)
RHS: (a, b) → zDelete → a+b → xCreate → (2(a+b), 0) = (2a+2b, 0)  ✓

Dual: X-copy ; swap ; Z-merge = X-delete ; Z-create.

LHS: (a, b) → (2a,2b,2b,2a) → swap → (2a,2b,2b,2a) → zMerge → (2a, 2a)
RHS: (a, b) → xDelete → 2a → zCreate → (2a, 2a)  ✓
-/

theorem hopf_spinor : ∀ (ψ : Spinor1),
    xMerge (spinorSwap (zCopy ψ)) = xCreate (zDelete ψ) := by
  intro ψ; ext <;> simp [zCopy, spinorSwap, xMerge, zDelete, xCreate] <;> ring

theorem hopf_spinor_x : ∀ (ψ : Spinor1),
    zMerge (spinorSwap (xCopy ψ)) = zCreate (xDelete ψ) := by
  intro ψ; ext <;> simp [xCopy, spinorSwap, zMerge, xDelete, zCreate] <;> ring

/-! ### Z/X spider semantics (1,1) and Hadamard -/

/-- Z-rotation on Spinor1: R(α) = [[cos(α/2), -sin(α/2)], [sin(α/2), cos(α/2)]] -/
noncomputable def zSpider_1_1 (α : ℝ) : Spinor1 → Spinor1 := fun ψ =>
  ⟨Real.cos (α/2) * ψ.c0 - Real.sin (α/2) * ψ.c1,
   Real.sin (α/2) * ψ.c0 + Real.cos (α/2) * ψ.c1⟩

/-- Hadamard (unnormalized): H = [[1,1],[1,-1]], H·(c0,c1) = (c0+c1, c0-c1) -/
def hadamard : Spinor1 → Spinor1 := fun ψ =>
  ⟨ψ.c0 + ψ.c1, ψ.c0 - ψ.c1⟩

/-- X-rotation: X(α) = H · Z(α) · H (color change) -/
noncomputable def xSpider_1_1 (α : ℝ) : Spinor1 → Spinor1 :=
  fun ψ => hadamard (zSpider_1_1 α (hadamard ψ))

/-! ### Spinor qubit space (for spinor semantics, n ≤ 2 suffices for Hopf) -/

def SpinorQubitSpace : Nat → Type
  | 0 => ℝ
  | 1 => Spinor1
  | 2 => Spinor2
  | _ => Unit  -- placeholder for n ≥ 3

/-! ### Spinor spider semantics (0-phase only, for Hopf) -/

noncomputable def spinorZSpider_1_2 : Spinor1 → Spinor2 := zCopy
noncomputable def spinorZSpider_2_1 : Spinor2 → Spinor1 := zMerge
noncomputable def spinorZSpider_1_0 : Spinor1 → ℝ := zDelete
noncomputable def spinorXSpider_0_1 : ℝ → Spinor1 := xCreate
noncomputable def spinorXSpider_1_2 : Spinor1 → Spinor2 := xCopy
noncomputable def spinorXSpider_2_1 : Spinor2 → Spinor1 := xMerge
noncomputable def spinorXSpider_1_0 : Spinor1 → ℝ := xDelete
noncomputable def spinorZSpider_0_1 : ℝ → Spinor1 := zCreate

def spinorSwapOp : Spinor2 → Spinor2 := spinorSwap

/-! ### Hopf diagram semantics (LHS and RHS) -/

/-- LHS of Hopf: zCopy ; swap ; xMerge -/
noncomputable def hopfLHS : Spinor1 → Spinor1 :=
  fun ψ => xMerge (spinorSwap (zCopy ψ))

/-- RHS of Hopf: zDelete ; xCreate -/
noncomputable def hopfRHS : Spinor1 → Spinor1 :=
  fun ψ => xCreate (zDelete ψ)

theorem hopfLHS_eq_hopfRHS : hopfLHS = hopfRHS := by
  funext ψ; exact hopf_spinor ψ

/-- Dual Hopf LHS: xCopy ; swap ; zMerge -/
noncomputable def hopfDualLHS : Spinor1 → Spinor1 :=
  fun ψ => zMerge (spinorSwap (xCopy ψ))

/-- Dual Hopf RHS: xDelete ; zCreate -/
noncomputable def hopfDualRHS : Spinor1 → Spinor1 :=
  fun ψ => zCreate (xDelete ψ)

theorem hopfDualLHS_eq_hopfDualRHS : hopfDualLHS = hopfDualRHS := by
  funext ψ; exact hopf_spinor_x ψ

end SpinorModule

end ZXClifford.Semantics
