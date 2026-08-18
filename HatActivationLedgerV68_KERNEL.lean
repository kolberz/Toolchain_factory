import HatActivationLedgerV68_SEALED

namespace HatV68Kernel

open HatV68Sealed

/-- Kernel-reduced counterpart of the low-order Hat ledger bound. -/
theorem hat_low_order_kernel_lt :
    ledgerBound hatGroups < 176005 / 10000000 := by
  decide

/-- Kernel-reduced counterpart of the low-order triangular ledger bound. -/
theorem triangular_low_order_kernel_lt :
    ledgerBound triangularGroups < 255629 / 10000000 := by
  decide

/-- Kernel-reduced registered-tail Hat certificate. -/
theorem hat_registered_final_kernel_lt :
    ledgerBound hatGroups + registeredTail < 18291 / 1000000 := by
  decide

/-- Kernel-reduced registered-tail triangular certificate. -/
theorem triangular_registered_final_kernel_lt :
    ledgerBound triangularGroups + registeredTail < 26253 / 1000000 := by
  decide

#print axioms hat_low_order_kernel_lt
#print axioms triangular_low_order_kernel_lt
#print axioms hat_registered_final_kernel_lt
#print axioms triangular_registered_final_kernel_lt

end HatV68Kernel
