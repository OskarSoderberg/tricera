package tricera.postprocessor

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.theories.{Theory, TheoryCollector}
import tricera.concurrency.CCReader.FunctionContext
import IExpression.Predicate

class PostconditionSimplifier private (var contexts: Map[String, FunctionContext]) extends SolutionProcessor {

    def apply(contexts : Map[String, FunctionContext]) : PostconditionSimplifier =
        new PostconditionSimplifier(contexts)

    def isPostcondition(funName : String, predName : String) = {
        funName match {
            case fun : String if (predName.startsWith(fun + "_post")) => true
            case _ => false
        }
    }

    def simplifyPostcondition(precondition : IFormula, 
                              postcondition : IFormula,
                              simplifiedPostcondition : IFormula) : (IFormula, Boolean) = {
        SimpleAPI.withProver { p =>
            import p._
            import IExpression._
            import ap.parser.VariableSubstVisitor
            import ap.SimpleAPI.ProverStatus
            import ap.SimpleAPI.TimeoutException

            /* val prc = IEquation(ISortedVariable(1, Sort.Integer), IIntLit(8))
            val poc = ISortedQuantified(Quantifier.EX, Sort.Integer, IEquation(ISortedVariable(0, Sort.Integer), ISortedVariable(1, Sort.Integer)).&(prc)) 
            val pocs = ISortedQuantified(Quantifier.EX, Sort.Integer, IEquation(ISortedVariable(0, Sort.Integer), ISortedVariable(1, Sort.Integer)).&(IBoolLit(true)))
            
            val f = prc.===>((poc).<===>(pocs)) */
            val f = precondition.==>(postcondition.<=>(simplifiedPostcondition))

            val maxQuantifierDepth = MaxQuantifierDepthVisitor.countMaxQuantifierDepth(f)
            val maxIndex = MaxIndexVisitor.countMaxIndex(f)
            /* println("-- maxQuantifierDepth: " + maxQuantifierDepth)
            println("-- maxIndex: " + maxIndex) */
            val freeVarsCount = (maxIndex)
            /* println("-- freeVarsCount: " + freeVarsCount) */
            val constants = p.createConstants("c", 0 to freeVarsCount).toList
            val formula = VariableSubstVisitor(f.asInstanceOf[IFormula], (constants, 0))

            val theories : Seq[Theory] = {
                val coll = new TheoryCollector
                coll(formula)
                coll.theories
            }
            addTheories(theories)
            /* println("-- theories: " + theories) */

            println("-- formula (pre ==> (post <=> simplify(post))): \n")
            PrintIExpressionVisitor(formula)
            
            /* println("-- Solving riddle ...") */
            ??(formula)
            val result = try withTimeout(100) {
                ???
            } catch {
                case x: SimpleAPI.SimpleAPIException if x == TimeoutException => None
            }
            /* println("-- result: " + result) */
            var success = false
            val pc : IExpression = result match {
                case ProverStatus.Valid => 
                    success = true
                    simplifiedPostcondition 
                case _ =>
                    success = false
                    postcondition
            }
            
            (pc.asInstanceOf[IFormula], success)
        }
    }

    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        // treats one predicate solution
        val expr = solution(predicate).asInstanceOf[IFormula]
        contexts.keys.find(predicate.name.startsWith(_)) match {
            case Some(funName) if (isPostcondition(funName, predicate.name)) => 
                val functionContext = contexts(funName)
                val precondition = solution(functionContext.prePred.pred).asInstanceOf[IFormula]
                /* println("=== Simplifying: ======================================================")
                println("-- funName: " + funName)
                println("-- predicate: " + predicate)
                println("-- predicate.name: " + predicate.name)
                println("-- functionContext: " + functionContext)
                println("-- argNames: \n" + functionContext.prePredACSLArgNames)
                println("-- precondition: \n" + precondition)
                println("-- postcondition: \n" + expr)
                println("-- Starting iteration") */
                var postcondition = expr
                var i = 0
                var cont = true
                while (cont) {
                    /* println("---- Iteration:" + i) */
                    //println("---- postcondition: \n")
                    //PrintIExpressionVisitor(postcondition)
                    ReplaceNthFormula(postcondition, i) match {
                        case (simplifiedPostcondition, None) => 
                            cont = false
                        case (simplifiedPostcondition, Some(replacedFormula)) =>
                            /* println("-- replacedFormula: \n") */
                            /* PrintIExpressionVisitor(replacedFormula) */
                            //println("-- simplifiedPostcondition: \n")
                            //PrintIExpressionVisitor(simplifiedPostcondition)
                            simplifyPostcondition(precondition.asInstanceOf[IFormula], 
                                                  postcondition.asInstanceOf[IFormula], 
                                                  simplifiedPostcondition.asInstanceOf[IFormula]) match {
                                case (newPostcondition, success) =>
                                    postcondition = newPostcondition
                            }	
                    }
                    i = i + 1
                }
                /* println("===================================================================") */
                CleanupVisitor.cleanup(postcondition)
            case _ => expr
        }
    }

    class ReplaceNthFormulaVisitor(n: Int) extends CollectingVisitor[Unit, IExpression] {
        private var formulaCount = 0
        private var formula : Option[IExpression] = None

        override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
            case f: IFormula if formulaCount == n =>
                formula = Some(f)
                formulaCount += 1
                ShortCutResult(IBoolLit(true))
            case f: IFormula =>
                formulaCount += 1
                KeepArg
            case _ =>
                KeepArg
        }

        override def postVisit(t: IExpression, arg: Unit, subres: Seq[IExpression]): IExpression = {
            t.update(subres)
        }

        def getReplacedFormula : Option[IExpression] = formula
    }

    object ReplaceNthFormula {
        def apply(expr: IExpression, n: Int): (IExpression, Option[IExpression]) = {
            val visitor = new ReplaceNthFormulaVisitor(n)
            val newExpr = visitor.visit(expr, ())
            (newExpr, visitor.getReplacedFormula)
        }
    }

    class GetNthFormulaVisitor(n: Int) extends CollectingVisitor[Unit, Option[IExpression]] {
        private var formulaCount = 0
        private var formula : Option[IFormula] = None

        override def preVisit(t: IExpression, arg: Unit): PreVisitResult = {
            formula match {
                case Some(f) => ShortCutResult(Some(f))
                case _ =>
                    t match {
                        case f: IFormula if formulaCount == n =>
                            formulaCount += 1
                            formula = Some(f)
                            KeepArg
                        case f: IFormula =>
                            formulaCount += 1
                            KeepArg
                        case _ =>
                            KeepArg
                    }
            }
        }
            
        override def postVisit(t: IExpression, arg: Unit, subres: Seq[Option[IExpression]]): Option[IExpression] = {
            formula match {
                case Some(f) => Some(f)
                case _ => None
            }
        }
    }

    object GetNthFormulaVisitor {
        def apply(expr: IExpression, n: Int): Option[IExpression] = {
            val visitor = new GetNthFormulaVisitor(n)
            visitor.visit(expr, None)
        }
    }

}

object PostconditionSimplifier {
    def apply(contexts: Map[String, FunctionContext]) : PostconditionSimplifier =
        new PostconditionSimplifier(contexts)
}


class PrintIExpressionVisitor extends CollectingVisitor[Int, IExpression] {
        import ap.types.Sort

        override def preVisit(t: IExpression, depth: Int): PreVisitResult = t match {
            case IBinFormula(IBinJunctor.And, _, _) => 
                println(" " * depth + "&")
                UniSubArgs(depth + 2)
            case IBinFormula(IBinJunctor.Or, _, _) => 
                println(" " * depth + "|")
                UniSubArgs(depth + 2)
            case IBinFormula(IBinJunctor.Eqv, _, _) => 
                println(" " * depth + "<->")
                UniSubArgs(depth + 2)
            case INot(_) => 
                println(" " * depth + "!")
                UniSubArgs(depth + 2)
            case IEquation(_, _) =>
                println(" " * depth + "=")
                UniSubArgs(depth + 2)
            case IIntFormula(IIntRelation.EqZero, _) =>
                println(" " * depth + "= 0")
                UniSubArgs(depth + 2)
            case IIntFormula(IIntRelation.GeqZero, _) =>
                println(" " * depth + ">= 0")
                UniSubArgs(depth + 2)
            case ISortedQuantified(quan, sort, f) =>
                println(" " * depth + quan + (if (sort == Sort.Integer) " " else (" " + sort.toString + ". ")))
                UniSubArgs(depth + 2)
            case f : IFormula =>
                println(" " * depth + "[f]" + f)
                UniSubArgs(depth + 2)
            case default =>
                println(" " * depth + default)
                ShortCutResult(default)
        }

        override def postVisit(t: IExpression, depth: Int, subres: Seq[IExpression]): IExpression = {
            t update subres
        }
    }

    object PrintIExpressionVisitor {
        def apply(expr: IExpression): IExpression = {
            val visitor = new PrintIExpressionVisitor
            visitor.visit(expr, 0)
        }
    }


class IFormulaCounterVisitor extends CollectingVisitor[Unit, Int] {

    override def postVisit(t: IExpression, arg: Unit, subres: Seq[Int]): Int = t match {
        case f : IFormula => subres.sum + 1
        case _ => subres.sum
    }
}

object IFormulaCounterVisitor {
    def countIFormulas(expr: IExpression): Int = {
        val counter = new IFormulaCounterVisitor
        counter.visit(expr, ())
    }
}

class CleanupVisitor extends CollectingVisitor[Unit, IExpression] {

    override def postVisit(t: IExpression, arg: Unit, subres: Seq[IExpression]): IExpression = t match {
        case IBinFormula(IBinJunctor.And, f1, f2) if (f1 == IBoolLit(true)) => f2
        case IBinFormula(IBinJunctor.And, f1, f2) if (f2 == IBoolLit(true)) => f1
        case IBinFormula(IBinJunctor.And, f1, f2) if (f1 == IBoolLit(false) || f2 == IBoolLit(false)) => false
        case IBinFormula(IBinJunctor.Or, f1, f2) if (f1 == IBoolLit(true)) => f1
        case IBinFormula(IBinJunctor.Or, f1, f2) if (f2 == IBoolLit(true)) => f2
        case IBinFormula(IBinJunctor.Or, f1, f2) if (f1 == IBoolLit(false)) => f2
        case IBinFormula(IBinJunctor.Or, f1, f2) if (f2 == IBoolLit(false)) => f1
        case ISortedQuantified(_, _, f) if (f == IBoolLit(true)) => IBoolLit(true)
        case ISortedQuantified(_, _, f) if (f == IBoolLit(false)) => IBoolLit(false)
        case INot(f) if (f == IBoolLit(true)) => IBoolLit(false) 
        case INot(f) if (f == IBoolLit(false)) => IBoolLit(true) 
        case _ => t
    }
}

object CleanupVisitor {
    def cleanup(expr: IExpression): IExpression = {
        val cleanupVisitor = new CleanupVisitor
        Rewriter.rewrite(expr, (t) => cleanupVisitor.visit(t, ()))
    }
}


class MaxQuantifierDepthVisitor extends CollectingVisitor[Int, Int] {

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {               
        case vb: IVariableBinder => UniSubArgs(quantifierDepth + 1)
        case _ => KeepArg
    }

    override def postVisit(t: IExpression, quantifierDepth: Int, subres: Seq[Int]): Int = 
        if (subres.isEmpty) quantifierDepth else subres.max

}

object MaxQuantifierDepthVisitor {
    def countMaxQuantifierDepth(expr: IExpression): Int = {
        val counter = new MaxQuantifierDepthVisitor
        counter.visit(expr, 0)
    }
}

class MaxIndexVisitor extends CollectingVisitor[Unit, Int] {

    override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {               
        case v: IVariable => ShortCutResult(v.index)
        case _ => KeepArg
    }

    override def postVisit(t: IExpression, arg: Unit, subres: Seq[Int]): Int = 
        if (subres.isEmpty) -1 else subres.max

}

object MaxIndexVisitor {
    def countMaxIndex(expr: IExpression): Int = {
        val counter = new MaxIndexVisitor
        counter.visit(expr, ())
    }
}