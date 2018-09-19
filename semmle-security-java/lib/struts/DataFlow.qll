import java
import semmle.code.java.dataflow.DataFlow
/** Contains data flow steps that are specific to apache struts2*/


/** A method in `ActionProxy` that may return remote user input. */
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

/** The class `ActionMapping`.*/
class ActionMapping extends RefType {
  ActionMapping() {
    hasQualifiedName("org.apache.struts2.dispatcher.mapper", "ActionMapping")    
  }
}

/** A method in `ActionMapper` that returns a field that may be tainted.*/
class ActionMappingGetMethod extends Method {
  ActionMappingGetMethod() {
    getDeclaringType() instanceof ActionMapping and
    (
      hasName("getName") or
      hasName("getNamespace") or
      hasName("getMethod") or
      hasName("getParams") or
      hasName("getExtension")
    )
  }
}

/** Holds if `source` is a remote user input in struts. */
predicate isRemoteUserInputSource(DataFlow::Node source) {
   source.asExpr().(MethodAccess).getMethod() instanceof ActionProxyGetMethod
}

/** Tracks through constructor and getter of `ActionMapping`.*/
predicate actionMapperEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(ConstructorCall c | c.getAnArgument() = node1.asExpr() and
    c.getConstructedType() instanceof ActionMapping and c = node2.asExpr()
  ) or
  exists(MethodAccess ma | ma.getMethod() instanceof ActionMappingGetMethod and
    node1.asExpr() = ma.getQualifier() and node2.asExpr() = ma
  )
}