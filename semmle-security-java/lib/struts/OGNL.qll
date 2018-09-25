import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.DataFlow3
import lib.dataflow_extra.CollectionsEdges
import lib.dataflow_extra.ExtraEdges
import lib.struts.Sanitizers
import lib.dataflow_extra.Sanitizers

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

/** Tracks parameters of a `Method` that ended up being evaluated as ognl.*/
class OgnlCallConfiguration extends DataFlow3::Configuration {
  OgnlCallConfiguration() {
    this = "OgnlCallConfiguration"
  }
  
  override predicate isSource(DataFlow::Node source) {
    exists(Method m | m.getAParameter() = source.asParameter() and
      source.asParameter().getType() instanceof TypeString
    )
  }
  
  override predicate isSink(DataFlow::Node sink) {
    isOgnlSink(sink)
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    standardExtraEdges(node1, node2) or
    collectionsPutEdge(node1, node2)
  }
  
  override predicate isBarrier(DataFlow::Node node) {
    ognlSanitizers(node) or
    node instanceof StrutsTestSanitizer or
    node instanceof ToStringSanitizer or
    node instanceof MapMethodSanitizer
  }
}

/** A `Method` whose parameter ended gets evaluated as ognl.*/
class OgnlCallMethod extends Method {
  OgnlCallMethod() {
    exists(OgnlCallConfiguration cfg, DataFlow::Node source |
      cfg.hasFlow(source, _) and source.asParameter() = this.getAParameter()
    ) and
    not hasName("completeExpressionIfAltSyntax") and
    not hasName("stripExpressionIfAltSyntax") and
    not hasName("setLocation")
  }
}

/** An `OgnlCallMethod` that is not used by another `OgnlCallMethod`.*/
class OgnlEntryPointMethod extends OgnlCallMethod {
  OgnlEntryPointMethod() {
    exists(Method m | m.polyCalls(this) and not m instanceof OgnlCallMethod)
  }
}