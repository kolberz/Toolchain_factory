import DAGRestrictionUpdate
import DAGSemiringSemantics
import DAGSupportSensitive
import DAGCofactorPair
import DAGAllocatorContract
import DAGReferenceAllocator

namespace DAGRestrictionUpdate

/-- Umbrella marker: importing this module requires the semantic, generalized
semiring, support-sensitive, paired-cofactor, allocator-contract, and concrete
reference-allocator layers to have all replayed successfully in the same Lean
environment. -/
theorem certifiedCore_marker : True := by
  trivial

#print axioms certifiedCore_marker

end DAGRestrictionUpdate
