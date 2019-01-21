import cpp
import semmle.code.cpp.dataflow.DataFlow

/** An access to an operator stack variable, which are arguments to PostScript functions. */
predicate isOSPAccess(FieldAccess fa) {
  exists(FieldAccess opStack, FieldAccess stack | 
    fa.getTarget().hasName("p")
    | fa.getQualifier() = stack and stack.getTarget().hasName("stack") and
      stack.getQualifier() = opStack and opStack.getTarget().hasName("op_stack")
    )
}

/** A DataFlow::Node that is an access to an operator stack variable. */
predicate isOSPSource(DataFlow::Node source) {
  exists(FieldAccess fa | isOSPAccess(fa) and
      source.asExpr() = fa
    )
}