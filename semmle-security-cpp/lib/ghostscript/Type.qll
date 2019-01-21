import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.dataflow.DataFlow
/** Contains QL classes specific to various structures in Ghostscript. */

/** Access to a variable of type `ref` or various other equivalent types.*/
class RefAccess extends Expr {
  /** The variable of this `ref`*/
  Variable v;
  
  RefAccess() {
    (v.getAnAccess() = this or v.getAnAccess() = this.(AddressOfExpr).getAnOperand()) and 
    exists(string name | v.getType().getName() = name | 
      v.getType() instanceof PointerType or
      name = "os_ptr" or name = "const_os_ptr" or
      name = "const os_ptr" or name = "ref" or
      name = "const ref"
    )
  }
  
  Variable getVariable() {
    result = v
  }
  
  /** Convenient predicate to check that two access are to the same variable.*/
  predicate isEquivalent(RefAccess other) {
    this.getVariable() = other.getVariable()
  }
}

/** An access to a field that requires type checking.*/
class TypeFieldAccess extends FieldAccess {
  TypeFieldAccess() {
    exists(FieldAccess f | f.getTarget().hasName("value") and
      this.getQualifier() = f and this.getTarget().getDeclaringType().hasName("v")
    )
  }

  RefAccess getRef() {
    result = this.getQualifier().(FieldAccess).getQualifier()
  }
}

/** An access to a field that represents the type of a `ref`.*/
class TypeAttrAccess extends FieldAccess {
  TypeAttrAccess() {
    exists(FieldAccess fa | fa.getTarget().hasName("tas") and
      fa = this.getQualifier() and this.getTarget().getName() = "type_attrs"
    )
  }

  RefAccess getRef() {
    result = this.getQualifier().(FieldAccess).getQualifier()
  }
}

/** A comparison statement that is likely to be a type check. */
class TypeCheck extends TypeAttrAccess {
  TypeCheck() {
    exists(EqualityOperation eq | eq.getAnOperand().getAChild*() = this)
  }
}

/** A switch statement that uses the type of a `ref` as the condition. This is a common pattern for checking types. */
class SwitchCheck extends TypeAttrAccess {
  SwitchStmt stmt;
  SwitchCheck() {
    stmt.getControllingExpr().getAChild*() = this
  }
  
  SwitchStmt getSwitch() {
    result = stmt
  }
}

/** A DataFlow::Configuration to see whether a function checks the type of its argument.*/
class CheckTypeConfig extends DataFlow::Configuration {
  CheckTypeConfig() {
    this = "checkTypeConfig"
  }
  
  override predicate isSource(DataFlow::Node source) {
    exists(Parameter p | p = source.asParameter())
  }
  
  override predicate isSink(DataFlow::Node sink) {
    exists(TypeAttrAccess tc | tc.getRef() = sink.asExpr() and
      (tc instanceof TypeCheck or tc instanceof SwitchCheck)
    )
  }
}

/** A function that checks the type of a `ref` when it is passed as parameter `index`. */
class CheckFunction extends Function {
  int index;
  CheckFunction() {
    exists(CheckTypeConfig cfg, DataFlow::Node source | source.asParameter() = this.getParameter(index) and
      cfg.hasFlow(source, _)
    ) or
    //This allocates an array, so the parameter is overwritten and have array type afterwards. (i.e. Not user controlled anymore)
    (this.hasName("gs_alloc_ref_array") and index = 1)
  }
  
  int getIndex() {
    result = index
  }
}

/** A DataFlow::Node that can only be reached after a type check. */
predicate isTypeCheck(DataFlow::Node node) {
  exists(TypeAttrAccess tc, RefAccess e | dominates(tc, e) and 
    e = node.asExpr() and tc.getRef().isEquivalent(e) and 
    (tc instanceof TypeCheck or tc instanceof SwitchCheck)
  ) or
  exists(FunctionCall fc | 
    dominates(fc, node.asExpr()) and
    fc.getArgument(fc.getTarget().(CheckFunction).getIndex()).(RefAccess).isEquivalent(node.asExpr())
  )
}