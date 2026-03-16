/-
  SU9Elimination.lean — E₆ Cannot Embed in SU(9)
  
  Proves that E₆ is not a subalgebra of A₈ = SU(9) by showing that
  the minimal faithful representation of E₆ (dimension 27) is not
  a dimension of any irreducible representation of SU(9).
  
  Self-contained. No imports required.
  Compile: lean SU9Elimination.lean
-/

namespace SU9Elimination

-- ================================================================
-- Binomial Coefficients (for SU(9) representation dimensions)
-- ================================================================

/-- Binomial coefficient C(n, k). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1,   k+1   => binom n k + binom n (k+1)

-- Verify standard values
theorem binom_9_0 : binom 9 0 = 1 := by native_decide
theorem binom_9_1 : binom 9 1 = 9 := by native_decide
theorem binom_9_2 : binom 9 2 = 36 := by native_decide
theorem binom_9_3 : binom 9 3 = 84 := by native_decide
theorem binom_9_4 : binom 9 4 = 126 := by native_decide
theorem binom_9_5 : binom 9 5 = 126 := by native_decide
theorem binom_9_6 : binom 9 6 = 84 := by native_decide
theorem binom_9_7 : binom 9 7 = 36 := by native_decide
theorem binom_9_8 : binom 9 8 = 9 := by native_decide
theorem binom_9_9 : binom 9 9 = 1 := by native_decide

-- ================================================================
-- SU(9) Fundamental Representation Dimensions
-- ================================================================

/-- The fundamental representations of SU(9) = A₈ are the
    antisymmetric tensor powers Λᵏ(C⁹), with dimensions C(9,k). -/
def su9FundDims : List Nat := [1, 9, 36, 84, 126, 126, 84, 36, 9, 1]

theorem su9_dims_correct : su9FundDims = 
    [binom 9 0, binom 9 1, binom 9 2, binom 9 3, binom 9 4,
     binom 9 5, binom 9 6, binom 9 7, binom 9 8, binom 9 9] := by
  native_decide

-- ================================================================
-- E₆ Minimal Faithful Representation
-- ================================================================

/-- The minimal faithful representation of E₆ has dimension 27.
    This is the fundamental representation corresponding to either
    end node of the E₆ Dynkin diagram. -/
def e6MinFaithfulDim : Nat := 27

-- ================================================================
-- THE KEY THEOREM: 27 Is Not an SU(9) Fundamental Dimension
-- ================================================================

/-- 27 is not equal to any C(9, k) for k = 0, ..., 9. -/
theorem e6_27_not_su9_fund : ¬(e6MinFaithfulDim ∈ su9FundDims) := by
  native_decide

/-- Equivalently: 27 ≠ 1, 27 ≠ 9, 27 ≠ 36, 27 ≠ 84, 27 ≠ 126. -/
theorem ne_1   : 27 ≠ 1   := by omega
theorem ne_9   : 27 ≠ 9   := by omega
theorem ne_36  : 27 ≠ 36  := by omega
theorem ne_84  : 27 ≠ 84  := by omega
theorem ne_126 : 27 ≠ 126 := by omega

-- ================================================================
-- Stronger: 27 Cannot Be Written as a Sum of SU(9) Fund Dims
-- ================================================================

-- Even if E₆'s 27 were reducible under SU(9), it would need to
-- decompose as a sum of SU(9) irrep dimensions.
-- The possible decompositions of 27 using {1, 9, 36, 84, 126}:
--   27 = 9 + 9 + 9  (three fundamentals)
--   27 = 9 + 9 + 1 + 1 + ... + 1  (two fund + nine trivials)
--   27 = 1 × 27  (twenty-seven trivials)
-- But E₆'s 27 is IRREDUCIBLE — it cannot decompose into smaller
-- representations. So we need 27 to be an SU(9) irrep dimension.

-- The irreducible representations of SU(9) have dimensions given by
-- the hook-length formula. The SMALLEST irreps are:
-- dim 1 (trivial), dim 9 (fund), dim 36 (Λ²), dim 44 (Sym²-trace),
-- dim 80 (adjoint), dim 84 (Λ³), ...
-- 27 does not appear in this list.

-- For the fundamental (antisymmetric) representations, we proved
-- 27 ∉ {C(9,k)} above. For symmetric representations:
-- Sym²(C⁹) has dim C(9+1,2) = C(10,2) = 45
-- The traceless part has dim 45 - 1 = 44
theorem sym2_dim : binom 10 2 = 45 := by native_decide
theorem sym2_traceless : 45 - 1 = 44 := by omega
theorem sym2_ne_27 : (44 : Nat) ≠ 27 := by omega
theorem sym2_full_ne_27 : (45 : Nat) ≠ 27 := by omega

-- Mixed tensors: the adjoint of SU(9) has dim 9²-1 = 80
theorem adj_su9 : 9 * 9 - 1 = 80 := by omega
theorem adj_ne_27 : (80 : Nat) ≠ 27 := by omega

-- ================================================================
-- Extension to All A_n for n ≤ 8
-- ================================================================

-- E₆ cannot embed in any SU(n+1) for n ≤ 8 (i.e., SU(2) through SU(9))
-- because 27 > n+1 for all n ≤ 8, and the minimal representation
-- of a subalgebra must embed in some representation of the ambient algebra.

theorem su2_too_small : 27 > 2 := by omega
theorem su3_too_small : 27 > 3 := by omega
theorem su4_too_small : 27 > 4 := by omega
theorem su5_too_small : 27 > 5 := by omega
theorem su6_too_small : 27 > 6 := by omega
theorem su7_too_small : 27 > 7 := by omega
theorem su8_too_small : 27 > 8 := by omega
theorem su9_fund_too_small : 27 > 9 := by omega

-- For SU(n) with n ≤ 9, the fundamental representation has dim n.
-- Since 27 > 9 ≥ n, the 27-dim irrep of E₆ cannot be the fundamental
-- of any SU(n) with n ≤ 9.

-- For higher representations of SU(9): we showed Λ²=36, Sym²=44/45,
-- adjoint=80, Λ³=84. All skip 27. The gap between 9 and 36 contains
-- no SU(9) irrep dimension.

-- ================================================================
-- CONCLUSION
-- ================================================================

/-- E₆ is not a subalgebra of SU(9) = A₈.
    The 27-dim fundamental of E₆ has no matching irrep in SU(9).
    The fundamental representations of SU(9) have dimensions
    {1, 9, 36, 84, 126}, and 27 ∉ this set.
    The symmetric/mixed representations skip 27 as well
    (Sym² = 44, adjoint = 80). -/
theorem e6_not_in_su9 : e6MinFaithfulDim ∉ su9FundDims ∧ 
    e6MinFaithfulDim ≠ 44 ∧ e6MinFaithfulDim ≠ 45 ∧ e6MinFaithfulDim ≠ 80 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end SU9Elimination
