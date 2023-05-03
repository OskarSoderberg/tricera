package tricera.postprocessor

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.theories.{Theory, TheoryCollector}
import tricera.concurrency.CCReader.FunctionContext
import IExpression.Predicate

class ClauseRemover private (var contexts: Map[String, FunctionContext]) extends SolutionProcessor {

    def apply(contexts : Map[String, FunctionContext]) : ClauseRemover =
        new ClauseRemover(contexts)

    def isPostcondition(functionName : String, predicate : Predicate) : Boolean = {
        predicate.name.startsWith(functionName + "_post")
    }

    def isPrecondition(functionName : String, predicate : Predicate) : Boolean = {
        predicate.name.startsWith(functionName + "_pre")
    }

    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        // treats one predicate solution
        val functionName = contexts.keys.find(predicate.name.startsWith(_))
        functionName match {
            case Some(funName) => 
                if (isPostcondition(funName, predicate) ||
                    isPrecondition(funName, predicate)) {
                    val preOrPostcondition = solution(predicate)
                    println("pre or postcondition: \n" + preOrPostcondition)
                    val newPreOrPostcondition = TOHRemoverVisitor(preOrPostcondition, isPrecondition(funName, predicate))
                    CleanupVisitor.cleanup(newPreOrPostcondition)
                } else {
                    solution(predicate)
                }
            case None => solution(predicate) 
        }
    }
}

object ClauseRemover {
    def apply(contexts: Map[String, FunctionContext]) : ClauseRemover =
        new ClauseRemover(contexts)
}

class TOHRemoverVisitor(isPre: Boolean) extends CollectingVisitor[Int, IExpression] {

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {
        case default =>
            KeepArg
    }

    override def postVisit(t: IExpression, quantifierDepth: Int, subres: Seq[IExpression]): IExpression = t match {
        case IBinFormula(IBinJunctor.And, _, _) =>
            println("isPre: \n" + isPre)
            println("t: \n" + t)
            println("subres: " + subres)
            val f1 = subres(0)
            val f2 = subres(1)
            (ContainsTOHVisitor(f1, isPre), ContainsTOHVisitor(f2, isPre)) match {
                case (false, false) => 
                    println("doesn't contain TOH: " + f1)
                    println("doesn't contain TOH: " + f2)
                    t update subres
                case (true, false) => 
                    println("contains TOH: " + f1)
                    println("doesn't contain TOH: " + f2)
                    subres(1)
                case (false, true) => 
                    println("doesn't contain TOH: " + f1)
                    println("contains TOH: " + f2)
                    subres(0)
                case (true, true) => 
                    println("contains TOH: " + f1)
                    println("contains TOH: " + f2)
                    IBoolLit(true)
            }
        case q@ISortedQuantified(_,_,formula) =>
            println("quant formula: \n" + formula)
            println("quant subres: \n" + subres)
            q update subres
        case default => t update subres
    }
}

object TOHRemoverVisitor {
    def apply(expr: IExpression, isPre: Boolean): IExpression = {
        val removerVisitor = new TOHRemoverVisitor(isPre)
        removerVisitor.visit(expr, 0)
    }
}

class ContainsTOHVisitor(isPre: Boolean) extends CollectingVisitor[Unit, Boolean] {
    import ap.theories.Heap 

    override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {               
        case funAppTOH@IFunApp(heapFun@Heap.HeapFunExtractor(heapTheory), args) => 
            ShortCutResult(true)
        case _ => 
            KeepArg
    }

    override def postVisit(t: IExpression, arg: Unit, subres: Seq[Boolean]): Boolean = 
        if (subres.isEmpty) false else subres.reduce(_||_)

}

object ContainsTOHVisitor {
    def apply(expr: IExpression, isPre: Boolean): Boolean = {
        val visitor = new ContainsTOHVisitor(isPre: Boolean)
        visitor.visit(expr, false)
    }
}


