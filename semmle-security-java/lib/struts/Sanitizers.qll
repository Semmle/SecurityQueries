import java
import semmle.code.java.dataflow.DataFlow
import lib.dataflow_extra.Sanitizers
/** Contains sanitizers that are specific to apache struts 2.*/

/** A `MapMethodSanitizer` where the `Map` is the `ValueStackShadowMap`.*/
class StrutsMapMethodSanitizer extends MapMethodSanitizer {
  StrutsMapMethodSanitizer() {
    exists(Method m | (m.hasName("get") or m.hasName("containsKey")) and
      m.getDeclaringType().hasName("ValueStackShadowMap") and
      this.getEnclosingCallable() = m
    )   
  }
}

/** A `ToStringSanitizer` that corresponds to the `ActionMapping`'s `toString` method.*/
class StrutsToStringSanitizer extends ToStringSanitizer {
  StrutsToStringSanitizer() {
    exists(Method m | m.getDeclaringType().hasName("ActionMapping") and 
      m.hasName("toString") and this.getEnclosingCallable() = m
    )
  }
}