import java
import semmle.code.java.dataflow.DataFlow

/** A `Node` that is inside commonly used `Map` methods of rarely used subclasses of `Map`.*/
abstract class MapMethodSanitizer extends DataFlow::Node {
}

/** A `Node` that is inside the `toString` method of subclasses.*/
abstract class ToStringSanitizer extends DataFlow::Node {
}

/** Holds if `node` is inside test code. */
predicate isNodeInTestCode(DataFlow::Node node) {
  node.getEnclosingCallable() instanceof TestMethod
  or
  node.getEnclosingCallable().getDeclaringType() instanceof TestClass
  or
  node.asExpr().getFile().getAbsolutePath().toLowerCase().matches("%test%")
}