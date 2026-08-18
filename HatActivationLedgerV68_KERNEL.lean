import HatActivationLedgerV68_SEALED

namespace HatV68Kernel

open HatV68Sealed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel proof-producing low-order Hat ledger bound. -/
theorem hat_low_order_kernel_lt :
    ledgerBound hatGroups < 176005 / 10000000 := by
  norm_num [ledgerBound, hatGroups, contribution, activationWeight]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel proof-producing low-order triangular ledger bound. -/
theorem triangular_low_order_kernel_lt :
    ledgerBound triangularGroups < 255629 / 10000000 := by
  norm_num [ledgerBound, triangularGroups, contribution, activationWeight]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel proof-producing registered-tail Hat certificate. -/
theorem hat_registered_final_kernel_lt :
    ledgerBound hatGroups + registeredTail < 18291 / 1000000 := by
  norm_num [ledgerBound, hatGroups, contribution, activationWeight, registeredTail]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel proof-producing registered-tail triangular certificate. -/
theorem triangular_registered_final_kernel_lt :
    ledgerBound triangularGroups + registeredTail < 26253 / 1000000 := by
  norm_num [ledgerBound, triangularGroups, contribution, activationWeight, registeredTail]

#print axioms hat_low_order_kernel_lt
#print axioms triangular_low_order_kernel_lt
#print axioms hat_registered_final_kernel_lt
#print axioms triangular_registered_final_kernel_lt

end HatV68Kernel
