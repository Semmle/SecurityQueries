import java
import semmle.code.java.dataflow.DataFlow

/** Extra remote sources that comes from `ServletRequest`.*/
predicate extraRequestSource(DataFlow::Node source) {
  exists(Method m, MethodAccess ma | m.getName().matches("get%") and
    not (m.getName() = "getAttribute" or m.getName() = "getContextPath") |
    (m.getDeclaringType().getASupertype*().hasQualifiedName("javax.servlet.http", "HttpServletRequest") 
     or m.getDeclaringType().getASupertype*().hasQualifiedName("javax.servlet", "ServletRequest"))and
     source.asExpr() = ma and ma.getMethod() = m
  )
}