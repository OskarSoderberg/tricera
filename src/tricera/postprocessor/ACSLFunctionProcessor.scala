package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext


object ACSLFunctionProcessor {
    def apply(contexts: Map[String, FunctionContext]) : ACSLFunctionProcessor =
        new ACSLFunctionProcessor(contexts)
}

class ACSLFunctionProcessor(contexts: Map[String, FunctionContext]) extends SolutionProcessor {
    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        // assumes predicate is pre or postcondition
        val preOrPostcondition = solution(predicate)
        val functionName = contexts.keys.find(predicate.name.startsWith(_))
        functionName match {
            case Some(funName) if (isPrecondition(funName, predicate)) => 
                val rewriteVisitor = new ACSLFunctionRewriteVisitor(contexts(funName), true)
                rewriteVisitor.visit(preOrPostcondition, 0)
            case Some(funName) if (isPostcondition(funName, predicate)) => 
                val rewriteVisitor = new ACSLFunctionRewriteVisitor(contexts(funName), false)
                rewriteVisitor.visit(preOrPostcondition, 0)
            case _ => 
                preOrPostcondition
        }
    }

    def isPostcondition(functionName : String, predicate : Predicate) : Boolean = {
        predicate.name.startsWith(functionName + "_post")
    }

    def isPrecondition(functionName : String, predicate : Predicate) : Boolean = {
        predicate.name.startsWith(functionName + "_pre")
    }

    class ACSLFunctionRewriteVisitor(context: FunctionContext, isPre: Boolean) extends CollectingVisitor[Int, IExpression] {

        def getVarName(variableIndex: Int, quantifierDepth: Int) : String = {
            if (isPre) {
                context.prePredACSLArgNames(variableIndex - quantifierDepth)
            } else {
                context.postPredACSLArgNames(variableIndex - quantifierDepth)
            }
        }

        override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = {
            import ap.theories._
            t match { 
                case vb: IVariableBinder => 
                    UniSubArgs(quantifierDepth + 1)
                
                // is_O_Int(read(@h, a)) -> \valid(a)
                // FIX: ADT.CtorId(adt, sortNum) might match on default object
                case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), 
                                            Seq(IFunApp(readFun@Heap.HeapFunExtractor(heapTheory), 
                                                        Seq(h@ISortedVariable(hIndex, _), 
                                                            a@ISortedVariable(vIndex, _))))), 
                                    num)
                    if (readFun == heapTheory.read && getVarName(hIndex, quantifierDepth) == "@h") => {
                    ShortCutResult(IAtom(ACSLExpression.valid, Seq(a)))
                }

                // read(h,p).get_<sort> -> *p
                case IFunApp(getFun,
                            Seq(IFunApp(readFun@Heap.HeapFunExtractor(heapTheory), 
                                        Seq(heap@ISortedVariable(hIndex,_), 
                                            pointer@ISortedVariable(pIndex,_)))))
                        if (getFun.name.startsWith("get") && 
                            readFun == heapTheory.read && 
                            getVarName(hIndex, quantifierDepth) == "@h") => {
                    ShortCutResult(IFunApp(ACSLExpression.deref, Seq(pointer)))
                }

                // read(\old(@h), \old(p)) -> \old(*p)
                case IFunApp(getFun,
                             Seq(IFunApp(readFun@Heap.HeapFunExtractor(heapTheory), 
                                         Seq(oldHeap@ISortedVariable(hIndex,_), 
                                             oldPointer@ISortedVariable(pIndex,_)))))
                        if (getFun.name.startsWith("get") &&
                            readFun == heapTheory.read && 
                            getVarName(hIndex, quantifierDepth) == "\\old(@h)" && 
                            getVarName(pIndex, quantifierDepth).startsWith("\\old")) => {
                    ShortCutResult(IFunApp(ACSLExpression.oldDeref, Seq(oldPointer)))
                }
                case _ => KeepArg
            }
        }

        override def postVisit(t : IExpression, quantifierDepth: Int, subres : Seq[IExpression]) : IExpression = {
            import ap.theories.Heap
            t match {
                case _ => t update subres
            }
        }
    }
}