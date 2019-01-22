import cpp
import semmle.code.cpp.dataflow.TaintTracking
import lib.ghostscript.Type
import lib.ghostscript.Stack
/** Various dataflow utilities related to collections. */

/** A method that takes a collection as an input argument, and store the result in the output argument.*/
abstract class FetchMethod extends Function {
  
  abstract int getInput();
  
  abstract int getOutput();
}

/** FetchMethod for array.*/
class ArrayGetMethod extends FetchMethod {
  int input;
  int output;
  
  ArrayGetMethod() {
    this.hasName("array_get") and input = 1 and output = 3
  }
  
  override int getInput() {
    result = input
  }
  
  override int getOutput() {
    result = output
  }
}

/** FetchMethod for dictionary.*/
class DictionaryFetchMethod extends FetchMethod {
  int input;
  int output;
  
  DictionaryFetchMethod() {
    (this.hasName("dict_find_string") and input = 0 and output = 2) or
    (this.hasName("dict_find") and input = 0 and output = 2)
  }
  
  override int getInput() {
    result = input
  }
  
  override int getOutput() {
    result = output
  }
}

class InputSourceConfig extends DataFlow::Configuration {
  InputSourceConfig() {
    this = "inputSourceConfig"
  }
  
  override predicate isSource(DataFlow::Node source) {
    isOSPSource(source)
  }
  
  override predicate isSink(DataFlow::Node sink) {
    exists(FetchMethod f, FunctionCall fc | fc.getTarget() = f | 
      fc.getArgument(f.getOutput()).(RefAccess).getVariable().getAnAccess() = sink.asExpr() 
    )
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    isFetchEdge(node1, node2)
  }
}

predicate isFetchEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(FunctionCall fc, FetchMethod f | fc.getTarget() = f |
    node1.asExpr() = fc.getArgument(f.getInput()) and
    node2.asExpr() = fc.getArgument(f.getOutput()).(RefAccess).getVariable().getAnAccess() and
    node1.getEnclosingCallable() = node2.getEnclosingCallable()
  )
}