/**
 * @name Double Ognl Evaluation
 * @description Fields that are initialized from configuration that may get evaluated twice as Ognl expression.
 * @kind path-problem
 * @problem.severity error
 * @id double_eval
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.frameworks.Servlets
import semmle.code.java.dataflow.internal.DataFlowUtil
import lib.dataflow_extra.CollectionsEdges
import lib.dataflow_extra.ExtraEdges
import lib.struts.Sanitizers
import lib.struts.DataFlow
import lib.dataflow_extra.Sanitizers
import DataFlow::PathGraph
import lib.struts.OGNL

/** A `Field` whose value is a compile time constant.*/
class ConstantField extends Field {
  ConstantField() {
    exists(CompileTimeConstantExpr e | this.getAnAssignedValue() = e and
      this.isFinal()
    )
  }
}

/** A `Class` whose fields may be initialized from a config file.*/
class InputClass extends RefType {
  InputClass() {
    hasQualifiedName("org.apache.struts2.views.jsp", "StrutsBodyTagSupport") or
    hasQualifiedName("org.apache.struts2.components", "Component") or
    hasQualifiedName("com.opensymphony.xwork2", "Result") or
    hasQualifiedName("org.apache.struts.action", "Action") or
    hasQualifiedName("com.opensymphony.xwork2.interceptor", "Interceptor")
  }
}

/** A `Field` that may take value from a config file.*/
class ConfigurableField extends Field {
  ConfigurableField() {
    getDeclaringType().getASupertype*() instanceof InputClass
  }
}

/** Tracks from a field that may take value from configuration file into the an ognl evaluation method.*/
class InputCfg extends DataFlow::Configuration {
  InputCfg() {
    this = "input"
  }
  
  override predicate isSource(DataFlow::Node source) {
    exists(ConfigurableField f | f.getAnAccess() = source.asExpr() and
      not f instanceof ConstantField)
    or
    //`ActionConfig` params are also taken from configuration.
    exists(MethodAccess ma, Method m | ma.getMethod() = m and
      m.getDeclaringType().hasName("ActionConfig") and
      m.hasName("getParams") and source.asExpr() = ma
    )
  }
  
  override predicate isSink(DataFlow::Node sink) {
    exists(MethodAccess ma, OgnlEntryPointMethod entry, Method m | ma.getMethod() = m and
      ma.getAnArgument() = sink.asExpr() and entry.overridesOrInstantiates*(m)
    )
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    standardExtraEdges(node1, node2) or
    collectionsPutEdge(node1, node2) or
    actionMapperEdge(node1, node2)
  }

  override predicate isBarrier(DataFlow::Node node) {
    node instanceof StrutsTestSanitizer
    or
    ognlSanitizers(node)
    or
    node instanceof ToStringSanitizer
    or
    node instanceof MapMethodSanitizer
  }
}

class DoubleEvalConfig extends DataFlow::Configuration {
  DoubleEvalConfig() {
    this = "doubleEvalConfig"
  }
  
  override predicate isSource(DataFlow::Node source) {
    exists(MethodAccess ma, OgnlEntryPointMethod entry, Method m | ma.getMethod() = m and
      source.asExpr() = ma and entry.overridesOrInstantiates*(m)
    )
   }
  
  override predicate isSink(DataFlow::Node sink) {
    exists(MethodAccess ma, OgnlEntryPointMethod entry, Method m, int i | ma.getMethod() = m and
      sink.asExpr() = ma.getArgument(i) and entry.overridesOrInstantiates*(m) and
      m.getParameter(i).getType() instanceof TypeString
    ) or
    isOgnlSink(sink)
  }
  
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    standardExtraEdges(node1, node2) or
    collectionsPutEdge(node1, node2) or
    actionMapperEdge(node1, node2)
  }
  
  override predicate isBarrier(DataFlow::Node node) {
    ognlSanitizers(node) or
    node instanceof StrutsTestSanitizer or
    node instanceof ToStringSanitizer or
    node instanceof MapMethodSanitizer or
    //Stops when we reach an `OgnlEntryPointMethod` to cut down on duplicate results.
    exists(OgnlEntryPointMethod m, DataFlow::Node n |TaintTracking::localTaint(n, node) and m.getAParameter() = n.asParameter()) or
    exists(ReturnStmt stmt, DataFlow::Node rtn | stmt.getResult() = rtn.asExpr() and TaintTracking::localTaint(node, rtn) and
      stmt.getEnclosingCallable() instanceof OgnlEntryPointMethod)
  }
}

from DoubleEvalConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink,
InputCfg input, DataFlow::Node inputSrc, DataFlow::Node inputSink
where cfg.hasFlowPath(source, sink) and input.hasFlow(inputSrc, inputSink) and
//use call site of `InputCfg` as source of `DoubleEvalConfig`
exists(MethodAccess ma | ma = source.getNode().asExpr() and ma.getAnArgument() = inputSink.asExpr()) and
//Remove `circular` evaluations
not exists(MethodAccess ma | source.getNode().asExpr() = ma and sink.getNode().asExpr() = ma.getAnArgument()) and
//Cut down on paths that contains one another
not exists(DataFlow::Node s | TaintTracking::localTaintStep+(s, inputSrc))
select source, source, sink, "$@ from configuration first $@ and then evaluated $@.", inputSrc, "Input", source, "evaluated", sink, "here"