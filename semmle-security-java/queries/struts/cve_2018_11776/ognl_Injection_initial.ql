/**
 * @name Ognl injection
 * @description Identifies where remote user input may get evaluated as Ognl expression.
 * @kind path-problem
 * @problem.severity error
 * @id OgnlInjection
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.frameworks.Servlets
import semmle.code.java.dataflow.internal.DataFlowUtil
import DataFlow::PathGraph
import lib.struts.Sanitizers
import lib.dataflow_extra.ExtraEdges
import lib.dataflow_extra.CollectionsEdges
import lib.dataflow_extra.ExtraSources
import lib.struts.OGNL

class OgnlInjectionCfg extends DataFlow::Configuration {
  OgnlInjectionCfg() {
    this = "ognl injection initial"
  }
  
  override predicate isSource(DataFlow::Node source) {
    source instanceof RemoteUserInput or extraRequestSource(source)
  }
  
  override predicate isSink(DataFlow::Node sink) {
    isOgnlSink(sink)
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    standardExtraEdges(node1, node2) or
    collectionsPutEdge(node1, node2) or
    TaintTracking::localTaintStep(node1, node2) or
    taintStringFieldFromQualifier(node1, node2) or
    isTaintedFieldStep(node1, node2)
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

/** Tracks from tainted object to its field access when the field is of type string.*/
predicate taintStringFieldFromQualifier(DataFlow::Node node1, DataFlow::Node node2) {
  taintFieldFromQualifier(node1, node2) and
  exists(Field f | f.getAnAccess() = node2.asExpr() and f.getType() instanceof TypeString)
}

from OgnlInjectionCfg cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select source,source, sink, "$@ flows to here and is used in OGNL.", sink, "User input"