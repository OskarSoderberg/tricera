package tricera.postprocessor

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.theories.{Theory, TheoryCollector}
import tricera.concurrency.CCReader.FunctionContext
import IExpression.Predicate

object EqualityProcessor {
    def apply(contexts: Map[String, FunctionContext]) : EqualityProcessor =
        new EqualityProcessor(contexts)
}

class EqualityProcessor private (var contexts: Map[String, FunctionContext]) extends SolutionProcessor {

    def apply(contexts : Map[String, FunctionContext]) : EqualityProcessor =
        new EqualityProcessor(contexts)

    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        val functionName = contexts.keys.find(predicate.name.startsWith(_))
        functionName match {
            case Some(funName) => 
                if (isPostcondition(funName, predicate)) {
                    val postcondition = solution(predicate)
                    val functionContext = contexts(funName)
                    val precondition = solution(functionContext.prePred.pred).asInstanceOf[IFormula]

                    println("precondition \n" + precondition)
                    println("postcondition \n" + postcondition)
                    val equalityVisitor = new EqualityVisitor
                    equalityVisitor.visit(precondition, 0)
                    println("next")
                    equalityVisitor.visit(postcondition, 0)
                    val equalityMap = equalityVisitor.getEM
                    println(equalityMap)

                    /*
                    TODO: Replace precondition as well
                    */
                    val newPrecondition = EqualityMapReplacerVisitor.replace(precondition, equalityMap)
                    val newPostcondition = EqualityMapReplacerVisitor.replace(postcondition, equalityMap)

                    println(newPostcondition)

                    newPostcondition
                } else {
                    solution(predicate)
                }
            case None => solution(predicate)
        }
    }

    def isPostcondition(functionName : String, predicate : Predicate) : Boolean = {
        predicate.name.startsWith(functionName + "_post")
    }
}

case class EqualityTranslator(equals : Set[ITerm], target : ITerm)

case class EqualityMap(eqMap : Set[EqualityTranslator]) {

    def addEquality(equality : (ITerm, ITerm)) : EqualityMap = {
        equality match {
            case (term1, term2) =>
                val maybeTranslator1 = getTranslator(term1)
                val maybeTranslator2 = getTranslator(term2)
                (maybeTranslator1, maybeTranslator2) match {
                    case (Some(et1@EqualityTranslator(set1, target1)), Some(et2@EqualityTranslator(set2, target2))) =>
                        EqualityMap(eqMap.-(et1).-(et2).+(EqualityTranslator(set1 ++ set2, getPurest(target1, target2))))
                    case (Some(et@EqualityTranslator(set, target)), None) =>
                        EqualityMap(eqMap.-(et).+(EqualityTranslator(set.+(term2), getPurest(target, term2))))
                    case (None, Some(et@EqualityTranslator(set, target))) =>
                        EqualityMap(eqMap.-(et).+(EqualityTranslator(set.+(term1), getPurest(target, term1))))
                    case (None, None) =>
                        EqualityMap(eqMap.+(EqualityTranslator(Set(term1, term2), getPurest(term1, term2))))
                }
        }
    }

    def getPurest(term1 : ITerm, term2 : ITerm) : ITerm = {
        (term1, term2) match {
            case (t@ISortedVariable(_,_), _) => t
            case (_, t@ISortedVariable(_,_)) => t
            case (t@IIntLit(_), _) => t
            case (_, t@IIntLit(_)) => t
            case _ => term1
        }
    }

    def getTranslator(term : ITerm) : Option[EqualityTranslator] = {
        eqMap.find {
            case EqualityTranslator(set, _) if set.contains(term) => true
            case _ => false
        }
    }

    def getReplacement(term : ITerm) : Option[ITerm] = {
        getTranslator(term) match {
            case Some(et) => Some(et.target)
            case None => None
        }
    }
}

class EqualityVisitor extends CollectingVisitor[Int, IExpression] {
    var em = EqualityMap(Set())

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {
        /* case IEquation(term1, term2) =>
            addEquality(term1, term2)
            KeepArg */
        case b: IVariableBinder => UniSubArgs(quantifierDepth + 1)
        case e@IEquation(v1 : IVariable, v2 : IVariable) if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
            em = em.addEquality(VariableShiftVisitor(v1, quantifierDepth, -quantifierDepth), 
                                VariableShiftVisitor(v2, quantifierDepth,-quantifierDepth))
            println("eq (" + quantifierDepth + "): " + VariableShiftVisitor(v1, quantifierDepth, -quantifierDepth) + " = " +
                                VariableShiftVisitor(v2, quantifierDepth,-quantifierDepth))
            KeepArg
        case e@IEquation(v : IVariable, term) if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
            em = em.addEquality(VariableShiftVisitor(term, quantifierDepth, -quantifierDepth), 
                                VariableShiftVisitor(v, quantifierDepth,-quantifierDepth))
            println("eq (" + quantifierDepth + "): " + VariableShiftVisitor(term, quantifierDepth, -quantifierDepth) + " = " +
                                VariableShiftVisitor(v, quantifierDepth,-quantifierDepth))
            KeepArg
        case e@IEquation(term, v : IVariable) if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
            em = em.addEquality(VariableShiftVisitor(term, quantifierDepth, -quantifierDepth), 
                                VariableShiftVisitor(v, quantifierDepth,-quantifierDepth))
            println("eq (" + quantifierDepth + "): " + VariableShiftVisitor(term, quantifierDepth, -quantifierDepth) + " = " +
                                VariableShiftVisitor(v, quantifierDepth,-quantifierDepth))
            KeepArg
        case e@IIntFormula(IIntRelation.EqZero, term) if !ContainsQuantifiedVisitor(e, quantifierDepth) => 
            em = em.addEquality(VariableShiftVisitor(term, quantifierDepth, -quantifierDepth), 
                                VariableShiftVisitor(IIntLit(0), quantifierDepth,-quantifierDepth))
            println("eq (" + quantifierDepth + "): " + VariableShiftVisitor(term, quantifierDepth, -quantifierDepth) + " = " +
                             VariableShiftVisitor(IIntLit(0), quantifierDepth,-quantifierDepth))
            KeepArg
        case default =>
            KeepArg
    }

    override def postVisit(t: IExpression, quantifierDepth: Int, subres: Seq[IExpression]): IExpression = {
        t update subres
    }

    def getEM = em
}


class EqualityMapReplacerVisitor(equalityMap : EqualityMap) extends CollectingVisitor[Int, IExpression] {

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {        
        /* case IEquation(term1, term2) =>
            addEquality(term1, term2)
            KeepArg */
        case IEquation(v1 : IVariable, v2 : IVariable) =>
            ShortCutResult(t)
        case IEquation(v : IVariable, term) =>
            ShortCutResult(t)
        case IEquation(term, v : IVariable) =>
            ShortCutResult(t)
        case IIntFormula(IIntRelation.EqZero, term) => 
            ShortCutResult(t)
        case ISortedQuantified(_,_,_) =>  UniSubArgs(quantifierDepth + 1)
        case default =>
            KeepArg
    }

    override def postVisit(t: IExpression, quantifierDepth: Int, subres: Seq[IExpression]): IExpression = t match {
        case term : ITerm =>
            val res = t update subres
            val shiftedTerm = VariableShiftVisitor(term, quantifierDepth,-quantifierDepth)
            equalityMap.getReplacement(shiftedTerm) match {
                case Some(newShiftedTerm) =>
                    val newTerm = VariableShiftVisitor(newShiftedTerm, 0, quantifierDepth)
                    println("replacing " + term + " by " + newTerm)
                    newTerm
                case None =>
                    res
            }
        case default => t update subres
    }
}

object EqualityMapReplacerVisitor {
    def replace(expr: IExpression, em : EqualityMap): IExpression = {
        val replacerVisitor = new EqualityMapReplacerVisitor(em)
        replacerVisitor.visit(expr, 0)
    }
}

class ContainsQuantifiedVisitor extends CollectingVisitor[Int, Boolean] {

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {               
        case v: ISortedQuantified => UniSubArgs(quantifierDepth + 1)
        case ISortedVariable(index, _) =>
            if (index < quantifierDepth) 
                ShortCutResult(true)
            else
                ShortCutResult(false)
        case _ => KeepArg
    }

    override def postVisit(t: IExpression, quantifierDepth: Int, subres: Seq[Boolean]): Boolean = 
        if (subres.isEmpty) false else subres.reduce(_||_)

}

object ContainsQuantifiedVisitor {
    def apply(expr: IExpression, quantifierDepth: Int): Boolean = {
        val counter = new ContainsQuantifiedVisitor
        counter.visit(expr, quantifierDepth)
    }
}