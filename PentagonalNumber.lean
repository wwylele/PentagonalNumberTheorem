import PentagonalNumber.Complex
import PentagonalNumber.Generic
import PentagonalNumber.Old
import PentagonalNumber.PowerSeries
import PentagonalNumber.Partition

/-!
# Pentagonal number theorem

* For power series (`PowerSeries.lean`)
  * `multipliable_pentagonalLhs_powerSeries` - multipliability of LHS
  * `pentagonalNumberTheorem_powerSeries` - LHS = sum over Nat
    * `summable_pentagonalRhs_powerSeries` - summability of RHS
  * `pentagonalNumberTheorem_intPos_powerSeries` - LHS = sum over Int, classic order
    * `summable_pentagonalRhs_intPos_powerSeries` - summability of RHS
  * `pentagonalNumberTheorem_intNeg_powerSeries` - LHS = sum over Int, opposite order
    * `summable_pentagonalRhs_intNeg_powerSeries` - summability of RHS
* For real/complex numbers (`Complex.lean`)
  * `multipliable_pentagonalLhs_complex` - multipliability of LHS
  * `pentagonalNumberTheorem_complex` - LHS = sum over Nat
    * `summable_pentagonalRhs_complex` - summability of RHS
  * `pentagonalNumberTheorem_intPos_complex` - LHS = sum over Int, classic order
    * `summable_pentagonalRhs_intPos_complex` - summability of RHS
  * `pentagonalNumberTheorem_intNeg_complex` - LHS = sum over Int, opposite order
    * `summable_pentagonalRhs_intNeg_complex` - summability of RHS
* `Generic.lean` contains the algebraic part shared by both power series and real/complex numbers.

# Theorems about partition

* `Nat.Partition.sum_partition` - Pentagonal number recurrence for partitions

# Other files
* `Old.lean` contains a (very long) combinatorial proof of pentagonal number theorem

-/
