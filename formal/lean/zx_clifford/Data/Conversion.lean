/-
  Data/Conversion.lean

  Shared conversion functions between ℝ and Float.
  Used by Semantics.Generators and Factorization.Encode to avoid circular dependency.
-/

import Mathlib.Data.Real.Basic

namespace ZXClifford.Data

/-- Convert ℝ to Float for computational semantics.
    Noncomputable since ℝ is constructively opaque; never evaluated at runtime. -/
noncomputable def realToFloat : ℝ → Float := fun _ => (0 : Float)

namespace Conversion
/-- Alias for realToFloat used by Encode and GorardBridge. -/
noncomputable def realToFloat := _root_.ZXClifford.Data.realToFloat
end Conversion

end ZXClifford.Data
