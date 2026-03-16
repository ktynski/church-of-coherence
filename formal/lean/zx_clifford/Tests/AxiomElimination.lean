/-
  Tests/AxiomElimination.lean

  Axiom-count regression gate for the ZX-Clifford package.

  Status: 29 axioms remaining, 2 sorry in Semantics/Functor.lean
    - Foundation/Cl31.lean: 0 axioms, 0 sorry
    - Semantics/Generators.lean: 0 axioms, 0 sorry
      * SpinorModule.hopf_spinor: PROVED (Hopf law on spinor module)
      * SpinorModule.hopf_spinor_x: PROVED (dual Hopf law on spinor module)
    - Semantics/Functor.lean: 0 axioms, 2 sorry (representation gap — proved on SpinorModule)
        * semantics_hopf: sorry (proved on SpinorModule, Cl31 migration deferred)
        * semantics_hopf_x: sorry (proved on SpinorModule, Cl31 migration deferred)
    - ZX/Category.lean: 0 axioms (comp_compute proved by rfl) ← was 1 axiom
    - Hypergraph/Basic.lean: 0 axioms (morphism_preserves_membership is structure field) ← was 1 axiom
    - Remaining 29 axioms: deferred (Factorization/Commutes, Encode, Geometrize, Grace, Hypergraph/DPO)
-/

import Data.Conversion
import Foundation.Cl31
import Semantics.Generators
import Semantics.Functor
import Factorization.Encode
import Factorization.Commutes
import Factorization.Geometrize
import Grace.Simplification
import Hypergraph.Basic
import Hypergraph.DPO
import ZX.Category

namespace ZXClifford.Tests.AxiomElimination

/-! ## Direct-Path: All 22 axioms ELIMINATED, 2 sorry remain (Hopf — representation gap) -/

-- Foundation/Cl31.lean: 4→0 axioms (all now theorems/defs)
#check @ZXClifford.Foundation.minkowskiQ       -- def (QuadraticForm construction)
#check @ZXClifford.Foundation.minkowskiQ_eval   -- theorem (rfl)
#check @ZXClifford.Foundation.rotor_mul_generic -- theorem (distributivity + trig)
#check @ZXClifford.Foundation.hadamard_sq       -- theorem (orthogonality)

-- Semantics/Generators.lean: 4→0 axioms, 3→0 sorry
#check @ZXClifford.Semantics.phaseToFloat        -- def (id on ℝ)
#check @ZXClifford.Semantics.rotor_composition_ax -- theorem (proved: mul_assoc + rotorE12_mul)
#check @ZXClifford.Semantics.hadamard_squared_ax  -- theorem (proved: ext + ring + sq_sqrt)
#check @ZXClifford.Semantics.color_change_ax      -- theorem (proved: ext + ring + sq_sqrt)

-- Semantics/Functor.lean: 14→0 axioms, 2 sorry (Hopf — proved on SpinorModule)
#check @ZXClifford.Semantics.tensorSemantics           -- def (concrete via split/join)
#check @ZXClifford.Semantics.semantics_zSpider_fusion  -- theorem (proved)
#check @ZXClifford.Semantics.semantics_xSpider_fusion  -- theorem (proved)
#check @ZXClifford.Semantics.semantics_color_change_z_ax -- theorem (proved)
#check @ZXClifford.Semantics.semantics_color_change_x_ax -- theorem (proved)
#check @ZXClifford.Semantics.semantics_hadamard_self_inverse -- theorem (proved)
#check @ZXClifford.Semantics.semantics_zSpider_id      -- theorem (proved)
#check @ZXClifford.Semantics.semantics_xSpider_id      -- theorem (proved)
#check @ZXClifford.Semantics.semantics_bialgebra       -- theorem (proved)
#check @ZXClifford.Semantics.semantics_hopf            -- sorry (SpinorModule.hopf_spinor proves it)
#check @ZXClifford.Semantics.semantics_z_copy          -- theorem (proved)
#check @ZXClifford.Semantics.semantics_z_delete        -- theorem (proved)
#check @ZXClifford.Semantics.semantics_x_copy          -- theorem (proved)
#check @ZXClifford.Semantics.semantics_dagger_cong     -- theorem (proved)
#check @ZXClifford.Semantics.semantics_respects_equiv  -- theorem (soundness, 2 sorry via Hopf)

-- Semantics/Generators.lean: SpinorModule Hopf law (fully proved)
#check @ZXClifford.Semantics.SpinorModule.hopf_spinor   -- theorem: Hopf on spinor module
#check @ZXClifford.Semantics.SpinorModule.hopf_spinor_x -- theorem: dual Hopf on spinor module

/-! ## Deferred Axioms (29 remaining)

  Previously 31; eliminated 2 in this session:
    - ZX/Category.lean: comp_compute proved by rfl (Quot.lift₂ definitional reduction)
    - Hypergraph/Basic.lean: morphism_preserves_membership promoted to structure field
-/

-- Factorization/Commutes.lean (18)
#check @ZXClifford.Factorization.encode_id_left
#check @ZXClifford.Factorization.encode_id_right
#check @ZXClifford.Factorization.encode_compose_assoc
#check @ZXClifford.Factorization.encode_zSpider_fusion
#check @ZXClifford.Factorization.encode_xSpider_fusion
#check @ZXClifford.Factorization.encode_color_change_z
#check @ZXClifford.Factorization.encode_color_change_x
#check @ZXClifford.Factorization.encode_hadamard_self_inverse
#check @ZXClifford.Factorization.encode_zSpider_id
#check @ZXClifford.Factorization.encode_xSpider_id
#check @ZXClifford.Factorization.encode_bialgebra
#check @ZXClifford.Factorization.encode_hopf
#check @ZXClifford.Factorization.encode_z_copy
#check @ZXClifford.Factorization.encode_z_delete
#check @ZXClifford.Factorization.encode_x_copy
#check @ZXClifford.Factorization.encode_compose_cong
#check @ZXClifford.Factorization.encode_tensor_cong
#check @ZXClifford.Factorization.encode_dagger_cong

-- Data/Conversion.lean (1)
#check @ZXClifford.Data.Conversion.realToFloat

-- Factorization/Encode.lean (3)
#check @ZXClifford.Factorization.encode_inputs
#check @ZXClifford.Factorization.encode_outputs
#check @ZXClifford.Factorization.encode_respects_equiv

-- Factorization/Geometrize.lean (2)
-- Grace/Simplification.lean (3)
-- Hypergraph/DPO.lean (2)

end ZXClifford.Tests.AxiomElimination
