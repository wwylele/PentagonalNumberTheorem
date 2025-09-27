import PentagonalNumber.Complex
import PentagonalNumber.Generic
import PentagonalNumber.Old
import PentagonalNumber.PowerSeries
import PentagonalNumber.WIP_Partition

/-!
# Pentagonal number theorem

## Main theorems
* For power series
  * `multipliable_pentagonalLhs_powerSeries` - multipliability of LHS
  * `pentagonalNumberTheorem_powerSeries` - LHS = sum over Nat
    * `summable_pentagonalRhs_powerSeries` - summability of RHS
  * `pentagonalNumberTheorem_intPos_powerSeries` - LHS = sum over Int, classic order
    * `summable_pentagonalRhs_intPos_powerSeries` - summability of RHS
  * `pentagonalNumberTheorem_intNeg_powerSeries` - LHS = sum over Int, opposite order
    * `summable_pentagonalRhs_intNeg_powerSeries` - summability of RHS
* For complex numbers
  * `multipliable_pentagonalLhs_complex` - multipliability of LHS
  * `pentagonalNumberTheorem_complex` - LHS = sum over Nat
    * `summable_pentagonalRhs_complex` - summability of RHS
  * `pentagonalNumberTheorem_intPos_complex` - LHS = sum over Int, classic order
    * `summable_pentagonalRhs_intPos_complex` - summability of RHS
  * `pentagonalNumberTheorem_intNeg_complex` - LHS = sum over Int, opposite order
    * `summable_pentagonalRhs_intNeg_complex` - summability of RHS
* `partitionFunctionSum` - Recurrence formula for partition function using pentagonal numbers
  * This is still in the `Old.lean` file with complicated proof
-/
