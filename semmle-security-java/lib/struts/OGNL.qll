import java
import semmle.code.java.dataflow.DataFlow
/** Contains classes and predicates related to the use of ognl.*/

class OgnlUtil extends RefType {
  OgnlUtil() {
    hasQualifiedName("com.opensymphony.xwork2.ognl", "OgnlUtil")
  }
}

/** Holds when `sink` is an argument to a call that ended up executing it as ognl.*/
predicate isOgnlSink(DataFlow::Node sink) {
  exists(MethodAccess ma | (ma.getMethod().hasName("compileAndExecute")) and
    ma.getMethod().getDeclaringType() instanceof OgnlUtil and
    sink.asExpr() = ma.getArgument(0)
  )
}
