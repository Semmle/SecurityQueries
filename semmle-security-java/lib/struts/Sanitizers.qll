import java
import semmle.code.java.dataflow.DataFlow
import lib.dataflow_extra.Sanitizers
import OGNL
/** Contains sanitizers that are specific to apache struts 2.*/

/** A `MapMethodSanitizer` where the `Map` is the `ValueStackShadowMap`.*/
class StrutsMapMethodSanitizer extends MapMethodSanitizer {
  StrutsMapMethodSanitizer() {
    exists(Method m | (m.hasName("get") or m.hasName("containsKey") or m.hasName("entrySet")) and
      m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Map%") and
      this.getEnclosingCallable() = m
    )   
  }
}

/** A `ToStringSanitizer` that corresponds to the various `toString` method.*/
class StrutsToStringSanitizer extends ToStringSanitizer {
  StrutsToStringSanitizer() {
    exists(Method m | 
      m.hasName("toString") and this.getEnclosingCallable() = m
    )
  }
}

/** A `DataFlow::Node` that is inside test code. */
class StrutsTestSanitizer extends DataFlow::Node {
  StrutsTestSanitizer() {
    isNodeInTestCode(this) or
    this.getEnclosingCallable().getDeclaringType().getName().matches("%Mock%")
  }
}

/** Holds if a node flows into a sanitizer method that filters out ognl script.*/
predicate ognlSanitizers(DataFlow::Node node) {
  exists(MethodAccess ma, Method m | ma.getMethod() = m and m.hasName("callMethod") and
    ma.getAnArgument() = node.asExpr() and m.getDeclaringType() instanceof OgnlUtil
  ) or
  exists(MethodAccess ma, Method m | m.hasName("cleanupActionName") or m.hasName("cleanupMethodName") |
    m = ma.getMethod() and ma.getAnArgument() = node.asExpr() and
    m.getDeclaringType().hasQualifiedName("org.apache.struts2.dispatcher.mapper", "DefaultActionMapper")
  )
  or
  exists(VarAccess v | v.getVariable().getType() instanceof NumericType and node.asExpr() = v)
}