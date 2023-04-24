package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import IExpression.Predicate

object TOHProcessor extends SolutionProcessor {
    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        val expr = solution(predicate)
        Rewriter.rewrite(expr, rewritingRule) // repeatedly applies rewritingRule(expr) until fixpoint reached
    }

    object HeapRewriter extends CollectingVisitor[Object, IExpression] {
        //override def preVisit(t : IExpression, arg : Object) : PreVisitResult = {}

        private def leadsToOldHeap(t : IExpression) : Boolean = {
            import IExpression._
            t match {
                case v@ISortedVariable(_,_) =>
                    v.index == 0 //   HARD CODED: assuming \old(@h) is first variable
                case funApp@IFunApp(fun,_) if (fun.name == "write") => 
                    leadsToOldHeap(funApp.iterator.next())
                case _ => false
            }
        }

        private def getAssignments(t : IExpression) : Seq[(ITerm,ITerm)] = {
            import IExpression._
            t match {
                case funApp@IFunApp(fun,_) if (fun.name == "write") => 
                    val iterator = funApp.iterator
                    val next = iterator.next()
                    val p = iterator.next().asInstanceOf[ITerm] // second and third args of write are always ITerms?
                    val v = iterator.next().asInstanceOf[ITerm]
                    (p, v) +: getAssignments(next)
                case _ => Seq()
            }
        }

        override def postVisit(t : IExpression, arg : Object, subres : Seq[IExpression]) : IExpression = {
            import ap.theories._
            t match {

                // write(write(...write(@h, ptr1, val1)...)) -> *ptr1 == val1 && *ptr2 == val2 && ...
                // TODO: add condition on h variable (it has to be the heap)
                case e@IEquation(funApp@IFunApp(fun, _), h@ISortedVariable(_,_)) if leadsToOldHeap(funApp) => 
                    getAssignments(funApp).map{ case (p, v) => 
                        IEquation(p, v).asInstanceOf[IFormula] }.reduce(_ & _)
                case e@IEquation(h@ISortedVariable(_,_), funApp@IFunApp(fun, _)) if leadsToOldHeap(funApp) => // add condition that h is @h variable
                    getAssignments(funApp).map{ case (p, v) => 
                        IEquation(p, v).asInstanceOf[IFormula] }.reduce(_ & _)

                // is_O_Int(read(@h, a)) -> \valid(a)
                // TODO: add condition on h variable (it has to be the heap)
                //       ADT.CtorId(adt, sortNum) this might match on default object
                /* case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(IFunApp(readFun, Seq(h@ISortedVariable(_, _), a@ISortedVariable(_, _))))), num)
                    if (readFun.name == "read") =>
                        IEquation(IFunApp(new IFunction("\\valid", 1, false, false), Seq(a)), IIntLit(1)) */

                // o.get<sort>.O_<sort> -> o
                case IFunApp(o_SFun, Seq(IFunApp(getSFun, Seq(obj)))) if (getSFun.name.startsWith("get")
                                                                            && o_SFun.name.startsWith("O_")) =>
                    obj

                case _ => t
            }
        }
    }

    private def rewritingRule(expr : IExpression) : IExpression =
        HeapRewriter.visit(expr, null)
}