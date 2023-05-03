package tricera.postprocessor

import ap.parser._
import IExpression._

object ACSLExpression {
    val valid = new Predicate("valid", 1)
    val deref = new IFunction("deref", 1, false, false)
    val oldDeref = new IFunction("oldDeref", 1, false, false)
}