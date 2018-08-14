import java
import semmle.code.java.dataflow.DataFlow
/** General dataflow edges that are useful for hunting vulnerabilities but not included in the standard library.*/

/** Holds if `node1` is a tainted value assigned to a field and `node2` is an access to the field. This essentially
 *  says that if a field is assigned to a tainted value at some point, then any access to that field is considered tainted.
 *  This has high risk of producing FP, but worth a try to see what you get.
 */
predicate isTaintedFieldStep(DataFlow::Node node1, DataFlow::Node node2) {
  exists(Field f, RefType t | node1.asExpr() = f.getAnAssignedValue() and node2.asExpr() = f.getAnAccess() and
      node1.asExpr().getEnclosingCallable().getDeclaringType() = t and
      node2.asExpr().getEnclosingCallable().getDeclaringType() = t
  )  
}