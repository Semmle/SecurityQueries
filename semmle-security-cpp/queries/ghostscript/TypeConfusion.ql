/**
 * @name TypeConfusion
 * @description Type confusion in GhostScript.
 * @kind path-problem
 * @id type-confusion-final
 * @problem.severity error
 */

import cpp
import lib.ghostscript.CollectionsTracking
import lib.ghostscript.Type
import DataFlow::PathGraph

class TypeConfusionConfig extends TaintTracking::Configuration2 {
  TypeConfusionConfig() {
    this = "typeConfusionConfig"
  }
  
  override predicate isSource(DataFlow::Node source) {
    exists(InputSourceConfig cfg, DataFlow::Node input | cfg.hasFlow(input,  source))
  }
  
  override predicate isSink(DataFlow::Node sink) {
    exists(TypeFieldAccess tc | tc.getRef()  = sink.asExpr()
    )
  }
  
  override predicate isSanitizer(DataFlow::Node node) {
    isTypeCheck(node) or
    //Manually remove the assignment of this argument inside array_get is safe.
    exists(Function f | f.getName() = "array_get" and
      f.getParameter(3) = node.asParameter()
    )
  }
}

from InputSourceConfig inputCfg, TypeConfusionConfig cfg, DataFlow::Node sink, DataFlow::PathNode inputSource,
DataFlow::PathNode inputSink
where cfg.hasFlow(inputSink.getNode(), sink) and inputCfg.hasFlowPath(inputSource, inputSink)
select inputSink, inputSource, inputSink, "$@ flows to here and is used later without type check.", inputSource, "Function argument"