import Clifford
open Clifford

namespace AllNCheck

/-- The aggregate all-n chain: levels `n ≤ 5` from `cliffordChainS_of_le_five`, levels `n ≥ 3`
from `MorleyKernel.cliffordChainS_inf`. -/
theorem allN (n : ℕ) : CliffordChainS n := by
  by_cases h : n ≤ 5
  · exact cliffordChainS_of_le_five h
  · exact Clifford.MorleyKernel.cliffordChainS_inf n (by omega)

#print axioms allN
end AllNCheck
