import java
import semmle.code.java.dataflow.DataFlow

/** A `Node` that is inside commonly used `Map` methods of rarely used subclasses of `Map`.*/
abstract class MapMethodSanitizer extends DataFlow::Node {
}

/** A `Node` that is inside the `toString` method of subclasses.*/
abstract class ToStringSanitizer extends DataFlow::Node {
}