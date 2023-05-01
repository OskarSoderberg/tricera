package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import IExpression.Predicate

object TOHProcessor extends SolutionProcessor {
    def apply(predicate : Predicate, solution : SolutionProcessor.Solution) : IExpression = {
        val expr = solution(predicate)
        Rewriter.rewrite(expr, rewritingRule) // repeatedly applies rewritingRule(expr) until fixpoint reached
    }

    object HeapRewriter extends CollectingVisitor[Unit, IExpression] {
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
                case funApp@IFunApp(fun, Seq(next,p,v)) if (fun.name == "write") => 
                    val assignment = (p.asInstanceOf[ITerm], v.asInstanceOf[ITerm])
                    assignment +: getAssignments(next)
                case _ => Seq()
            }
        }

        /* override def preVisit(t: IExpression, arg: Unit): PreVisitResult = {
            import ap.theories._
            t match { 
                case e@IEquation(funApp@IFunApp(fun, _), h@ISortedVariable(_,_)) if leadsToOldHeap(funApp) => 
                    println("rewrite heap")
                    ShortCutResult(getAssignments(funApp).map{ case (p, v) => 
                        IEquation(p, v).asInstanceOf[IFormula] }.reduce(_ & _))
                    
                case e@IEquation(h@ISortedVariable(_,_), funApp@IFunApp(fun, _)) if leadsToOldHeap(funApp) => // add condition that h is @h variable
                    println("rewrite heap")
                    ShortCutResult(getAssignments(funApp).map{ case (p, v) => 
                        IEquation(p, v).asInstanceOf[IFormula] }.reduce(_ & _))

                // o.get<sort>.O_<sort> -> o
                case IFunApp(o_SFun@Heap.HeapFunExtractor(heapTheory), 
                                Seq(IFunApp(getSFun, Seq(obj)))) if (getSFun.name.startsWith("get")
                                                                    && o_SFun.name.startsWith("O_")) =>
                    println("rewrite obj")
                    ShortCutResult(obj)

                // o.get<sort>.O_<sort> -> o
                case IFunApp(getSFun@Heap.HeapFunExtractor(heapTheory), 
                                Seq(IFunApp(o_SFun, Seq(obj)))) if (getSFun.name.startsWith("get")
                                                                    && o_SFun.name.startsWith("O_")) =>
                    println("rewrite obj")
                    ShortCutResult(obj)
                
                // read(write(h,p,o),p) -> o

                case _ => KeepArg
            }
        } */

        override def postVisit(t : IExpression, arg : Unit, subres : Seq[IExpression]) : IExpression = {
            import ap.theories.Heap
            t match {

                // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
                // TODO: add condition on h variable (it has to be the heap)
                // addresses must be separated
                case e@IEquation(funApp@IFunApp(fun@Heap.HeapFunExtractor(heapTheory), _), 
                                 h@ISortedVariable(_,_)) if leadsToOldHeap(funApp) => 
                    getAssignments(funApp).map{ 
                        case (p, v) => 
                            val function = heapTheory.userADTSels(0)(0) // HARD CODED FIRST SELECTOR! HOW TO GET TYPE?
                            IEquation(IFunApp(function, 
                                              Seq(IFunApp(heapTheory.read, 
                                                      Seq(h, p)))), 
                                      IFunApp(function, Seq(v))
                                      ).asInstanceOf[IFormula]
                        }.reduce(_ & _)
                
                case e@IEquation(h@ISortedVariable(_,_), 
                                 funApp@IFunApp(fun@Heap.HeapFunExtractor(heapTheory), _)) 
                                 if leadsToOldHeap(funApp) => // add condition that h is @h variable
                    getAssignments(funApp).map{ 
                        case (p, v) => 
                            val function = heapTheory.userADTSels(0)(0) // HARD CODED FIRST SELECTOR! HOW TO GET TYPE?
                            IEquation(IFunApp(function, 
                                              Seq(IFunApp(heapTheory.read, 
                                                      Seq(h, p)))), 
                                      IFunApp(function, Seq(v))
                                      ).asInstanceOf[IFormula]
                        }.reduce(_ & _)

                // o.get<sort>.O_<sort> -> o
                case IFunApp(o_SFun, Seq(IFunApp(getSFun, Seq(obj)))) if (getSFun.name.startsWith("get")
                                                                  && o_SFun.name.startsWith("O_")) =>
                    obj

                // o.O_<sort>.get<sort> -> o
                case IFunApp(getSFun, Seq(IFunApp(o_SFun, Seq(obj)))) if (getSFun.name.startsWith("get")
                                                                    && o_SFun.name.startsWith("O_")) =>
                    obj
                
                // read(write(h,p,o),p) -> o
                case IFunApp(readFun@Heap.HeapFunExtractor(heapTheory), 
                            Seq(IFunApp(writeFun, Seq(h, p2, o)), p1)) if (readFun == heapTheory.read
                                                                    && writeFun == heapTheory.write
                                                                    && p1 == p2) =>
                    o

                case _ => t update subres
            }
        }
    }

    private def rewritingRule(expr : IExpression) : IExpression = {
        HeapRewriter.visit(expr, null)
    }
}