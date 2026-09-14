import DAGRestrictionUpdate
import DAGSemiringSemantics
import DAGSupportSensitive
import DAGCofactorPair
import DAGAllocatorContract
import DAGReferenceAllocator
import DAGSharedMemo
import DAGOperationalMemo
import DAGOperationalMemoProof
import DAGOperationalMemoAllocation

namespace DAGRestrictionUpdate

/-- Umbrella marker: importing this module requires the semantic, generalized
semiring, support-sensitive, paired-cofactor, allocator-contract, and concrete
reference-allocator, shared-DAG, operational evaluator, semantic correctness,
and operational allocation layers to have all replayed successfully in the same Lean
environment. -/
theorem certifiedCore_marker : True := by
  trivial

#print axioms certifiedCore_marker

end DAGRestrictionUpdate
