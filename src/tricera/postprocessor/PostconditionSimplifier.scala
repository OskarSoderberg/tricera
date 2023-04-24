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

    def simplifyPostcondition(precondition : IExpression, 
                              postcondition : IExpression) : IExpression = {
        val substutor = new SubstituteNthIFormulaWithTrue(1)
        val simplifiedPostcondition = substutor.visit(postcondition, null).asInstanceOf[IFormula]
        println("subst: \n" + simplifiedPostcondition)
        SimpleAPI.withProver { p =>
            import p._
            import IExpression._
            import ap.parser.VariableSubstVisitor
            val formula = precondition.asInstanceOf[IFormula]
            
            val substFormula = VariableSubstVisitor(formula, 
                                     (List(IConstant(new ConstantTerm("x")),
                                           IConstant(new ConstantTerm("y")),
                                           IConstant(new ConstantTerm("z"))), 
                                      0))
            println("[substFormula structure]:\n")
            def printFirstRec(iexp : IExpression) : Unit = {

                println(iexp.iterator.toList.length + " " +  iexp.iterator
                                                            .toList
                                                            .map(el => "[" + el.getClass + ": " + el.toString + "]")
                                                            .mkString(", "))
                for (ie <- iexp.iterator.toList)
                printFirstRec(ie)
            }
            printFirstRec(substFormula)
            val theories : Seq[Theory] = {
                val coll = new TheoryCollector
                coll(substFormula)
                coll.theories
            }
            addTheories(theories)
            println(theories)
            //val formula = IEquation(IIntLit(1), IIntLit(1)) // Works, SAT
            println("formula: \n" + formula)
            println("substFormula: \n" + substFormula)
            
            println("Solving riddle ...")
            !!(substFormula) 
            
            println(???) /* fails: 
                "ap.api.SimpleAPI$SimpleAPIForwardedException: 
                    Internal exception: java.lang.ClassCastException: 
                        class ap.terfor.VariableTerm cannot be cast to class ap.terfor.ConstantTerm 
                        (ap.terfor.VariableTerm and ap.terfor.ConstantTerm are in unnamed module of 
                        loader 'app')"
                        */
            }
            postcondition
        }
                
    // addConstantsRaw(SymbolCollector constantsSorted formula)
    //.==>(postcondition.<=>(simplifiedPostcondition))
    // formula (\old(pre) ==> t == simplify(t))


    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        // treats one predicate solution
        val expr = solution(predicate).asInstanceOf[IFormula]
        contexts.keys.find(predicate.name.startsWith(_)) match {
            case Some(funName) if (isPostcondition(funName, predicate.name)) => 
                println("Simplifying: ======================================================")
                println("funName: " + funName)
                println("predicate: " + predicate)
                println("predicate.name: " + predicate.name)
                val functionContext = contexts(funName)
                println("functionContext: " + functionContext)
                println("argNames: \n" + functionContext.prePredACSLArgNames)
                val precondition = solution(functionContext.prePred.pred).asInstanceOf[IFormula]
                println("precondition: \n" + precondition)
                println("postcondition: \n" + expr)
                val simplifiedPostcondition = simplifyPostcondition(precondition, expr)
                println("simplifiedPostcondition: \n" + simplifiedPostcondition)
                println("================================================================")
                simplifiedPostcondition
            case _ => expr
        }
    }


    class SubstituteNthIFormulaWithTrue(n: Int) extends CollectingVisitor[Object, IExpression] {
        private var formulaCount: Int = 0

        override def preVisit(t: IExpression, arg: Object): PreVisitResult = t match {
            case f: IFormula if formulaCount == n =>
                formulaCount += 1
                ShortCutResult(IBoolLit(true))

            case f: IFormula =>
                formulaCount += 1
                KeepArg

            case _ => KeepArg
        }

        override def postVisit(t: IExpression, arg: Object, subres: Seq[IExpression]): IExpression = {
            t.update(subres)
        }
    }
}

object PostconditionSimplifier {
    def apply(contexts: Map[String, FunctionContext]) : PostconditionSimplifier =
        new PostconditionSimplifier(contexts)
}