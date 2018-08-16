import java
import semmle.code.java.dataflow.DataFlow
/** Contains data flow steps that are specific to apache struts2*/


/** The methods in `ActionProxy` that may return remote user input. */
class ActionProxyGetMethod extends Method {
  ActionProxyGetMethod() {
    getDeclaringType().getASupertype*().hasQualifiedName("com.opensymphony.xwork2", "ActionProxy") and
    (
      hasName("getMethod") or
      hasName("getNamespace") or
      hasName("getActionName")
    )
  }
}

/** Holds if `source` is a remote user input in struts. */
predicate isRemoteUserInputSource(DataFlow::Node source) {
   source.asExpr().(MethodAccess).getMethod() instanceof ActionProxyGetMethod
}