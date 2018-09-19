import java
import semmle.code.java.dataflow.DefUse
import semmle.code.java.dataflow.DataFlow
/** Contains DataFlow edges for handling access to Collections. These edges usually takes the approach of tainting the entire
 *  collection when an tainted element is added to the Collection and are considered too aggressive for default QL library.
 */

/** Tracks from a tainted Collection to an element of it iterated in a loop.*/
predicate forLoopEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(EnhancedForStmt for | for.getExpr() = node1.asExpr() and
    defUsePair(for.getVariable(), node2.asExpr().(VarAccess))
  )
}

/** Tracks from a tainted Map entry to the return of its `getKey` or `getValue` methods */
private predicate mapEntryEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | m.hasName("getKey") or m.hasName("getValue") |
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Map<>$Entry%") and
    ma.getMethod() = m and ma = node2.asExpr() and ma.getQualifier() = node1.asExpr()
  )
}

/** Tracks from a tainted Map to the return of its `get` or `getOrDefault` method. */
private predicate mapGetEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | m.hasName("get") or m.hasName("getOrDefault") |
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Map%") and
    ma.getMethod() = m and 
    ma = node2.asExpr() and ma.getQualifier() = node1.asExpr()
  )
}

/** Tracks from a tainted List to the return of various methods that outputs its elements or sublist.*/
private predicate listEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | ma.getMethod() =  m and
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.List%") and
    (
      m.getName() = "get" or
      m.getName() = "elementAt" or
      m.getName() = "elements" or
      m.getName() = "firstElement" or
      m.getName() = "lastElement" or
      m.getName() = "listIterator" or
      m.getName() = "subList"
    ) and
    ma = node2.asExpr() and ma.getQualifier() = node1.asExpr()
  ) or
  exists(MethodAccess ma, Method m | ma.getMethod() = m and
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.List%") and
    m.hasName("copyInto") and node1.asExpr() = ma.getQualifier() and node2.asExpr() = ma.getAnArgument()
  )
}

/** Tracks from a tainted Map to various of its internal data.*/
private predicate keyEntryEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | 
      m.hasName("entrySet") or m.hasName("keySet") or m.hasName("values") |
      node1.asExpr() = ma.getQualifier() and node2.asExpr() = ma and
      ma.getMethod() = m and
      m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Map%")
  )
}

/** Tracks from a tainted element into a Map. Note that this taints the whole map and can increase FP significantly.*/
private predicate mapPutEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | m = ma.getMethod() and 
    (
     m.hasName("put") or m.hasName("putAll") or m.hasName("replace") or m.hasName("putIfAbsent") or
     m.hasName("replaceAll") or m.hasName("compute") or m.hasName("computeIfAbsent") or m.hasName("merge")
    ) 
    and
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Map%") and
    ma.getAnArgument() = node1.asExpr() and ma.getQualifier() = node2.asExpr()
  )
}

/** Tracks from a tainted Collection to various methods that transforms it into different data type.*/
private predicate collectionTransformEdge(DataFlow::Node node1, DataFlow::Node node2) {
  exists(MethodAccess ma, Method m | ma.getMethod() =  m and
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Collection%") and
    (
      m.getName() = "stream" or
      m.getName() = "iterator" or
      m.getName() = "toArray" or
      m.getName() = "parallelStream"
    ) and
    ma = node2.asExpr() and ma.getQualifier() = node1.asExpr()
  ) or
  exists(MethodAccess ma, Method m | ma.getMethod() =  m and
    m.getDeclaringType().getASourceSupertype*().getQualifiedName().matches("java.util.Collection%") and
    (
      m.getName() = "toArray"    
    ) and
    ma.getQualifier() = node1.asExpr() and ma.getAnArgument() = node2.asExpr()
  )  
}

/** Tracks from a tainted Collection to its elements or other representations of its data.*/
predicate collectionsGetEdge(DataFlow::Node node1, DataFlow::Node node2) {
  collectionTransformEdge(node1, node2) or
  keyEntryEdge(node1, node2) or
  listEdge(node1, node2) or
  mapGetEdge(node1, node2) or
  mapEntryEdge(node1, node2)
}

/** Tracks from an element into a tainted Collection. Taints the whole collection and may cause significant increase in FP.*/
predicate collectionsPutEdge(DataFlow::Node node1, DataFlow::Node node2) {
  mapPutEdge(node1, node2)
}