/**
 * @name cve-2018-11776 final
 * @description Final query for detecting CVE-2018-11776 in Struts.
 * @kind path-problem
 * @id cve_2018_11776_final
 */


import java
import lib.struts.DataFlow
import lib.struts.OGNL
import lib.struts.Sanitizers
import lib.dataflow_extra.ExtraEdges
import DataFlow::PathGraph
import semmle.code.java.dataflow.TaintTracking


class MappingCfg extends DataFlow::Configuration {
  MappingCfg() {
    this = "cve 2018-11776"
  }
  
  override predicate isSource(DataFlow::Node source) {
    isRemoteUserInputSource(source)
  }
  
  override predicate isSink(DataFlow::Node sink) {
    isOgnlSink(sink)
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    TaintTracking::localAdditionalTaintStep(node1, node2) or
    isTaintedFieldStep(node1, node2)
  }
}

from MappingCfg cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select source,source, sink, "$@ flows to here and is used in OGNL.", source, "User input"