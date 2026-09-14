import DAGRestrictionUpdate
import DAGSemiringSemantics
import DAGSupportSensitive
import DAGCofactorPair
import DAGAllocatorContract

namespace DAGRestrictionUpdate

/-- Umbrella marker: importing this module requires the semantic, generalized
semiring, support-sensitive, paired-cofactor, and allocator-contract layers to
have all replayed successfully in the same Lean environment. -/
theorem certifiedCore_marker : True := by
  trivial

#print axioms certifiedCore_marker

end DAGRestrictionUpdate
