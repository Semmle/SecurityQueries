import java
import semmle.code.java.dataflow.DataFlow
/** Contains classes and predicates related to the use of ognl.*/

/** Holds when `sink` is an argument to a call that ended up executing it as ognl.*/
predicate isOgnlSink(DataFlow::Node sink) {
  exists(MethodAccess ma | (ma.getMethod().hasName("compileAndExecute")) and
    ma.getMethod().getDeclaringType().getName().matches("OgnlUtil") and
    sink.asExpr() = ma.getArgument(0)
  )
}
