/**
 * Copyright (c) 2020-2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package tricera.postprocessor

import ap.Signature
import ap.theories.{ADT, ModuloArithmetic, MulTheory}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Quantifier
import ap.parser._
import IExpression.Sort
import Sort.:::

object ACSLLineariser {

  def apply(formula : IFormula, signature : Signature) = {
    val order = signature.order

    //println("// Generated by Princess (http://www.philipp.ruemmer.org/princess.shtml) }")

    // declare the various kinds of constants
    for ((name, consts) <- List(("universalConstants", signature.universalConstants),
                                ("existentialConstants", signature.existentialConstants),
                                ("functions", signature.nullaryFunctions)))
      if (!consts.isEmpty) {
        println("\\" + name + " {")
        for (c <- consts)
          println("int " + c.name + ";")
        println("}")
      }

    // declare the required predicates
    if (!order.orderedPredicates.isEmpty) {
      println("\\predicates {")
      for (pred <- order.orderedPredicates) {
        print(pred.name)
        if (pred.arity > 0) {
          print("(")
          print((for (_ <- List.range(0, pred.arity)) yield "int") mkString ", ")
          print(")")
        }
        println(";")
      }
      println("}")
    }

    println("\\problem {")
    printExpression(formula, Seq()) // CHECK
    println
    println("}")
  }

  def printExpression(e : IExpression, acslArgNames : Seq[String]) = {
    val enriched = EnrichingVisitor.visit(e, ())
    HeapyPrinter.visit(enriched, PrintContext(List(), "", 0, acslArgNames))
  }

  def asString(e : IExpression, acslArgNames : Seq[String]) : String =
    ap.DialogUtil.asString { printExpression(e, acslArgNames) }

  private def fun2Identifier(fun : IFunction) = fun.name

  //////////////////////////////////////////////////////////////////////////////

  private val NonEqPredicate   = new Predicate ("!=", 2)
  private val GeqPredicate     = new Predicate (">=", 2)
  private val LtPredicate      = new Predicate ("<", 2)
  private val MinusFunction    = new IFunction ("-", 2, false, false)

  /**
   * Visitor to introduce some operations purely used for pretty-printing
   * purposes.
   */
  private object EnrichingVisitor extends CollectingVisitor[Unit, IExpression] {

    override def preVisit(t : IExpression,
                          oldCtxt : Unit) : PreVisitResult = t match {
      case IExpression.Difference(NonNegTerm(s), NonNegTerm(t)) =>
        TryAgain(IFunApp(MinusFunction, List(s, t)), ())

      case INot(IExpression.Eq(s, t)) =>
        TryAgain(IAtom(NonEqPredicate, List(s, t)), ())
      case IExpression.Geq(s, t) =>
        TryAgain(IAtom(GeqPredicate, List(s, t)), ())
      case INot(IExpression.Geq(s, t)) =>
        TryAgain(IAtom(LtPredicate, List(s, t)), ())

      case _ : IEquation =>
        KeepArg
      case IExpression.Eq(s, t) =>
        TryAgain(IEquation(s, t), ())

      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression,
                  ctxt : Unit, subres : Seq[IExpression]) : IExpression =
      t update subres
  }

  //////////////////////////////////////////////////////////////////////////////

  private case class PrintContext(vars : List[String],
                                  parentOp : String,
                                  outerPrec : Int,
                                  acslArgNames : Seq[String]) {
    def pushVar(name : String)          = PrintContext(name :: vars, parentOp, outerPrec, acslArgNames)
    def setParentOp(op : String)        = PrintContext(vars, op, outerPrec, acslArgNames)
    def addParentOp(op : String)        = PrintContext(vars, op + parentOp, outerPrec, acslArgNames)
    def setOpPrec(op : String, l : Int) = PrintContext(vars, op, l, acslArgNames)
    def addOpPrec(op : String, l : Int) = PrintContext(vars, op + parentOp, l, acslArgNames)
    def setPrecLevel(l : Int)           = PrintContext(vars, parentOp, l, acslArgNames)
  }

  private object AtomicTerm {
    def unapply(t : IExpression) : Option[ITerm] = t match {
      case t : IConstant => Some(t)
      case t : IVariable => Some(t)
      case t@IFunApp(_, Seq()) => Some(t)
      case _ => None
    }
  }

  private def atomicTerm(t : ITerm,
                         ctxt : PrintContext,
                         cast2Int : Boolean = false) : String = t match {
    case IConstant(c) ::: SortNeedingIntCast(_) if cast2Int =>
      c.name + ".\\as[int]"
    case IConstant(c) =>
      c.name
    case IVariable(index) => {
      var vs = ctxt.vars
      var ind = index

      while (ind > 0 && !vs.isEmpty) {
        vs = vs.tail
        ind = ind - 1
      }

      if (vs.isEmpty)
        ctxt.acslArgNames(ind)
      else
        vs.head
    }
    case IFunApp(f, Seq()) ::: SortNeedingIntCast(_) if cast2Int =>
      f.name + ".\\as[int]"
    case IFunApp(f, Seq()) =>
      f.name
  }

  private object SortNeedingIntCast {
    def unapply(sort : Sort) : Option[Sort] = sort match {
      case Sort.Numeric(_) => None
      case _               => Some(sort)
    }
  }

  private object NonNegTerm {
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case ITimes(coeff, s) if coeff.signum < 0 => None
      case IIntLit(value)   if value.signum < 0 => None
      case _                                    => Some(t)
    }
  }

  private def needsIntCast(t : ITerm) : Boolean = t match {
    case (_ : IConstant) ::: SortNeedingIntCast(_)       => true
    case IFunApp(MulTheory.Mul(), _)                     => false
    case (_ : IFunApp) ::: SortNeedingIntCast(_)         => true
    case _                                               => false
  }

  private def maybeInsertIntCast(t : ITerm,
                                 ctxt : PrintContext) : PrintContext =
    if (needsIntCast(t))
      insertIntCast(ctxt)
    else
      ctxt

  private def insertIntCast(ctxt : PrintContext) : PrintContext =
    ctxt.addOpPrec(".\\as[int]", 10)

  private def relation(rel : IIntRelation.Value) = rel match {
    case IIntRelation.EqZero => " == "
    case IIntRelation.GeqZero => ">="
  }

  private def precLevel(e : IExpression) : Int = e match {
    case IBinFormula(IBinJunctor.Eqv, _, _)             => 0
    case IBinFormula(IBinJunctor.Or, _, _)              => 0
    case IBinFormula(IBinJunctor.And, _, _)             => 0
    case _ : ITermITE | _ : IFormulaITE                 => 1
    case _ : INot | _ : IQuantified | _ : INamedPart |
         _ : ITrigger | _ : IEpsilon                    => 3
    case _ : IIntFormula | _ : IEquation |
         IAtom(NonEqPredicate | GeqPredicate |
               LtPredicate, _)                          => 4
    case IFunApp(MinusFunction, _)                      => 5
    case _ : IPlus                                      => 5
    case _ : ITimes | IFunApp(MulTheory.Mul(), _)       => 7
    case IIntLit(v) if (v.signum < 0)                   => 8
    case _ : ITerm | _ : IBoolLit | _ : IAtom           => 10
  }

  //////////////////////////////////////////////////////////////////////////////

  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {

    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
        List(ctxt setParentOp lastOp))
    }

    private def noParentOp(ctxt : PrintContext) = UniSubArgs(ctxt setParentOp "")

    private def shortCut(ctxt : PrintContext) = {
      print(ctxt.parentOp)
      ShortCutResult(())
    }

    private def tryAgainWithCast(s : ITerm, ctxt : PrintContext) =
      TryAgain(s, maybeInsertIntCast(s, ctxt))

    override def preVisit(t : IExpression,
                          oldCtxt : PrintContext) : PreVisitResult = {
      // first use the precedence level of operators to determine whether we
      // have to insert parentheses

      val newPrecLevel = precLevel(t)

      val ctxt =
        if (newPrecLevel > oldCtxt.outerPrec) {
          oldCtxt setPrecLevel newPrecLevel
        } else if (newPrecLevel < oldCtxt.outerPrec) {
          // then we need parentheses
          print("(")
          return TryAgain(t, oldCtxt.setOpPrec(")" + oldCtxt.parentOp, newPrecLevel))
        } else {
          oldCtxt
        }

      t match {
        // Terms

        case AtomicTerm(t) => {
          print(atomicTerm(t, ctxt))
          noParentOp(ctxt)
        }
        case IIntLit(value) => {
          print(value)
          noParentOp(ctxt)
        }

        case IPlus(t1, t2) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " + "),
            maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MulTheory.Mul(), Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " * "),
            maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MinusFunction, Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " - "),
            maybeInsertIntCast(t2, ctxt setParentOp "" setPrecLevel 6)))
        }

        case ITimes(coeff, s) => {
          print(coeff + "*")
          // noParentOp(ctxt)
          UniSubArgs(maybeInsertIntCast(s, ctxt setParentOp ""))
        }

        case IFunApp(ADT.TermSize(adt, num), Seq(t ::: tSort))
          if (adt sorts num) == tSort => {
          print("\\size(")
          allButLast(ctxt setPrecLevel 0, ", ", ")", 1)
        }

        case IFunApp(ModuloArithmetic.mod_cast,
        Seq(IIntLit(lower), IIntLit(upper), t)) =>
          TryAgain(t, ctxt.addOpPrec(".\\as[" +
            ModuloArithmetic.ModSort(lower, upper) +
            "]", 10))

        case IFunApp(ModuloArithmetic.int_cast, Seq(t)) =>
          TryAgain(t, insertIntCast(ctxt))

        case IFunApp(ModuloArithmetic.bv_extract,
        Seq(IIntLit(upper), IIntLit(lower), t)) =>
          TryAgain(t, ctxt.addOpPrec("[" + upper + ":" + lower + "]", 10))

        case IFunApp(fun, _) => {
          if (fun.arity == 1) {
            allButLast(ctxt setPrecLevel 0, ".", "." + fun2Identifier(fun), 1)
          } else if (fun.arity > 0) { // todo: should not be possible in ACSL
            print(fun2Identifier(fun))
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", fun.arity)
          } else {
            print(fun2Identifier(fun))
            KeepArg
          }
        }

        case _ : ITermITE | _ : IFormulaITE => {
          print("\\if (")
          SubArgs(List(ctxt setParentOp ") \\ then (",
            ctxt setParentOp ") \\ else (",
            ctxt setParentOp ")"))
        }

        // General formulae

        case IBinFormula(IBinJunctor.Or, INot(left : IAtom), right) => {
          left match {
            case IAtom(pred, Seq()) =>
              print(pred.name)
            case left =>
              // In this special case, recursively print the antecedent
              AbsyPrinter.visit(left, ctxt.setOpPrec("", 1))
          }

          print(" -> ")

          val newRightCtxt = right match {
            case IBinFormula(IBinJunctor.Or, INot(_), _) =>
              ctxt
            case _ =>
              ctxt setPrecLevel 1
          }

          TryAgain(right, newRightCtxt)
        }

        case IBinFormula(junctor, left, right) => {
          val op = junctor match {
            case IBinJunctor.And => " && "
            case IBinJunctor.Or => " || "
            case IBinJunctor.Eqv => " <-> "
          }

          val newLeftCtxt = left match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec(op, 1)
            case _ =>
              ctxt setParentOp op
          }
          val newRightCtxt = right match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec("", 1)
            case _ =>
              ctxt setParentOp ""
          }

          SubArgs(List(newLeftCtxt, newRightCtxt))
        }

        case IBoolLit(value) => {
          print("\\" + value)
          noParentOp(ctxt)
        }

        // ADT expressions

        case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
        num) => {
          print("is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
            "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case IAtom(NonEqPredicate,
        Seq(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
        IExpression.Const(num))) => {
          print("!is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
            "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case IExpression.Eq(t, ADT.BoolADT.True) =>
          TryAgain(t, ctxt)

        case IExpression.Eq(t, ADT.BoolADT.False) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case IAtom(NonEqPredicate, Seq(t, ADT.BoolADT.True)) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case IAtom(NonEqPredicate, Seq(t, ADT.BoolADT.False)) =>
          TryAgain(t, ctxt)

        // Equation predicates

        case IAtom(NonEqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " != ", "", 2)
        case IAtom(GeqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " >= ", "", 2)
        case IAtom(LtPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " < ", "", 2)

        case IEquation(s, t) =>
          allButLast(ctxt setPrecLevel 1, " == ", "", 2)

        // Atoms

        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }

        // Non-negated relations

        case IIntFormula(rel, _) => {
          UniSubArgs(ctxt setParentOp (" " + relation(rel) + " 0"))
        }

        case INot(subF) => {
          print("!")
          noParentOp(
            subF match {
              case _ : IIntFormula =>
                ctxt setPrecLevel 10
              case _ =>
                ctxt
            })
        }

        case ISortedQuantified(quan, sort, subF) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => "\\forall"
            case Quantifier.EX => "\\exists"
          })
          print(" " + sort + " " + varName)

          var newCtxt = ctxt pushVar varName

          var sub = subF
          while (sub.isInstanceOf[IQuantified] &&
            sub.asInstanceOf[IQuantified].quan == quan &&
            sub.asInstanceOf[IQuantified].sort == sort) {
            val varName2 = "v" + newCtxt.vars.size
            newCtxt = newCtxt pushVar varName2
            print(", " + varName2)
            val IQuantified(_, newSub) = sub
            sub = newSub
          }

          print("; ")
          TryAgain(sub, newCtxt)
        }

        case ISortedEpsilon(sort, _) => {
          val varName = "v" + ctxt.vars.size
          print("\\eps " + sort + " " + varName + "; ")
          noParentOp(ctxt pushVar varName)
        }
        case INamedPart(name, _) => {
          if (name != PartName.NO_NAME)
            print("\\part[" + name + "] ")
          noParentOp(ctxt)
        }
        case ITrigger(trigs, _) => {
          print("{")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
            yield (ctxt setParentOp ", ")) ++
            List(ctxt setParentOp "} ", ctxt setParentOp ""))
        }
      }
    }

    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)

  }

  private object HeapyPrinter extends CollectingVisitor[PrintContext, Unit] {

    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
        List(ctxt setParentOp lastOp))
    }

    private def noParentOp(ctxt : PrintContext) = UniSubArgs(ctxt setParentOp "")

    private def shortCut(ctxt : PrintContext) = {
      print(ctxt.parentOp)
      ShortCutResult(())
    }

    private def tryAgainWithCast(s : ITerm, ctxt : PrintContext) =
      TryAgain(s, maybeInsertIntCast(s, ctxt))

    private def handleFun(fun : IFunction, ctxt : PrintContext) = { // this handles TOH functions
      if (fun.arity == 1) {
        val printParentheses = (fun.name != "*")
        print(fun2Identifier(fun))
        if (printParentheses) {
          print("(")
        }
        
        val separator = if (printParentheses) "," else ""
        // print("CTXT: " + ctxt) 
        allButLast(ctxt setPrecLevel 0, separator, if (printParentheses) ")" else "", 1)
        //SubArgs(List(ctxt setParentOp ")" setPrecLevel 0))
      } else if (fun.arity > 0) { // todo: should not be possible in ACSL
        print(fun2Identifier(fun))
        print("(")
        allButLast(ctxt setPrecLevel 0, ", ", ")", fun.arity)
      } else {
        print(fun2Identifier(fun))
        KeepArg
      }
    }

    private def getVarName(index : Int, ctxt : PrintContext) : String = {
      val isHeapVar = (index >= ctxt.vars.length)
      if (isHeapVar)
        ctxt.acslArgNames(index - ctxt.vars.length) // IS THIS REALLY CORRECT??
      else
        ctxt.vars(index)
    }

    override def preVisit(t : IExpression,
                          oldCtxt : PrintContext) : PreVisitResult = {
      import ap.theories.Heap
      // first use the precedence level of operators to determine whether we
      // have to insert parentheses

      val newPrecLevel = precLevel(t)

      val ctxt =
        if (newPrecLevel > oldCtxt.outerPrec) {
          oldCtxt setPrecLevel newPrecLevel
        } else if (newPrecLevel < oldCtxt.outerPrec) {
          // then we need parentheses
          print("(")
          return TryAgain(t, oldCtxt.setOpPrec(")" + oldCtxt.parentOp, newPrecLevel))
        } else {
          oldCtxt
        }

      t match {
        // Terms

        /* case ISortedVariable(index, _) => {
          print(getVarName(index, ctxt))
          noParentOp(ctxt) // is this correct?
        }  */

        case AtomicTerm(t) => {
          print(atomicTerm(t, ctxt))
          noParentOp(ctxt)
        }
        case IIntLit(value) => {
          print(value)
          noParentOp(ctxt)
        }

        case IPlus(t1, t2) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " + "),
            maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MulTheory.Mul(), Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " * "),
            maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MinusFunction, Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " - "),
            maybeInsertIntCast(t2, ctxt setParentOp "" setPrecLevel 6)))
        }

        case ITimes(coeff, s) => {
          print(coeff + "*")
          // noParentOp(ctxt)
          UniSubArgs(maybeInsertIntCast(s, ctxt setParentOp ""))
        }

        case IFunApp(ADT.TermSize(adt, num), Seq(t ::: tSort))
          if (adt sorts num) == tSort => {
          print("\\size(")
          allButLast(ctxt setPrecLevel 0, ", ", ")", 1)
        }

        case IFunApp(ModuloArithmetic.mod_cast,
        Seq(IIntLit(lower), IIntLit(upper), t)) =>
          TryAgain(t, ctxt.addOpPrec(".\\as[" +
            ModuloArithmetic.ModSort(lower, upper) +
            "]", 10))

        case IFunApp(ModuloArithmetic.int_cast, Seq(t)) =>
          TryAgain(t, insertIntCast(ctxt))

        case IFunApp(ModuloArithmetic.bv_extract,
          Seq(IIntLit(upper), IIntLit(lower), t)) =>
            TryAgain(t, ctxt.addOpPrec("[" + upper + ":" + lower + "]", 10))

        // =========== EXPERIMENTS ===================
        

        // read(h,p) -> *p
        // TODO: Check that heap is @h
        // fix instances where *\old(b) should be \old(*b)
        case funapp@IFunApp(fun@Heap.HeapFunExtractor(heapTheory), Seq(heap@ISortedVariable(hIndex,_), pointer@ISortedVariable(pIndex,_))) 
          if (fun == heapTheory.read && getVarName(hIndex, ctxt) == "@h") => {
            print("*" + getVarName(pIndex, ctxt))
            shortCut(ctxt)
        }

        // read(\old(@h), \old(p)) -> \old(*p)
        case funapp@IFunApp(fun@Heap.HeapFunExtractor(heapTheory), Seq(oldHeap@ISortedVariable(hIndex,_), oldPointer@ISortedVariable(pIndex,_))) 
          if (fun == heapTheory.read && getVarName(hIndex, ctxt) == "\\old(@h)" 
                                     && getVarName(pIndex, ctxt).startsWith("\\old")) => {
            val oldWrappedVarName = getVarName(pIndex, ctxt)
            val varName = oldWrappedVarName.substring(5, oldWrappedVarName.length - 1)
            print("\\old(*" + varName + ")")
            shortCut(ctxt)
        }

        // is_O_Int(read(@h, a)) -> \valid(a)
        // FIX: ADT.CtorId(adt, sortNum) might match on default object
        case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(IFunApp(readFun@Heap.HeapFunExtractor(heapTheory), Seq(h@ISortedVariable(hIndex, _), a@ISortedVariable(vIndex, _))))), num)
          if (readFun == heapTheory.read && getVarName(hIndex, ctxt) == "@h") => {
            print("\\valid(" + getVarName(vIndex, ctxt) + ")")
            shortCut(ctxt)
          }
        
        case IFunApp(fun, _) => { // this handles TOH functions
          handleFun(fun, ctxt)
        }

        // =========== END EXPERIMENTS ===================

        case _ : ITermITE | _ : IFormulaITE => {
          print("\\if (")
          SubArgs(List(ctxt setParentOp ") \\ then (",
            ctxt setParentOp ") \\ else (",
            ctxt setParentOp ")"))
        }

        // General formulae

        case IBinFormula(IBinJunctor.Or, INot(left : IAtom), right) => {
          left match {
            case IAtom(pred, Seq()) =>
              print(pred.name)
            case left =>
              // In this special case, recursively print the antecedent
              HeapyPrinter.visit(left, ctxt.setOpPrec("", 1))
          }

          print(" -> ")

          val newRightCtxt = right match {
            case IBinFormula(IBinJunctor.Or, INot(_), _) =>
              ctxt
            case _ =>
              ctxt setPrecLevel 1
          }

          TryAgain(right, newRightCtxt)
        }

        case IBinFormula(junctor, left, right) => {
          val op = junctor match {
            case IBinJunctor.And => " && "
            case IBinJunctor.Or => " || "
            case IBinJunctor.Eqv => " <-> "
          }

          val newLeftCtxt = left match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec(op, 1)
            case _ =>
              ctxt setParentOp op
          }
          val newRightCtxt = right match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec("", 1)
            case _ =>
              ctxt setParentOp ""
          }

          SubArgs(List(newLeftCtxt, newRightCtxt))
        }

        case IBoolLit(value) => {
          print("\\" + value)
          noParentOp(ctxt)
        }

        // ADT expressions

        case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
        num) => {
          print("is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
            "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case IAtom(NonEqPredicate,
        Seq(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
        IExpression.Const(num))) => {
          print("!is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
            "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case IExpression.Eq(t, ADT.BoolADT.True) =>
          TryAgain(t, ctxt)

        case IExpression.Eq(t, ADT.BoolADT.False) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case IAtom(NonEqPredicate, Seq(t, ADT.BoolADT.True)) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case IAtom(NonEqPredicate, Seq(t, ADT.BoolADT.False)) =>
          TryAgain(t, ctxt)

        // Equation predicates

        case IAtom(NonEqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " != ", "", 2)
        case IAtom(GeqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " >= ", "", 2)
        case IAtom(LtPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " < ", "", 2)

        case IEquation(s, t) =>
          allButLast(ctxt setPrecLevel 1, " == ", "", 2)

        // Atoms

        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }

        // Non-negated relations

        case IIntFormula(rel, _) => {
          UniSubArgs(ctxt setParentOp (" " + relation(rel) + " 0"))
        }

        case INot(subF) => {
          print("!")
          noParentOp(
            subF match {
              case _ : IIntFormula =>
                ctxt setPrecLevel 10
              case _ =>
                ctxt
            })
        }

        case ISortedQuantified(quan, sort, subF) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => "\\forall"
            case Quantifier.EX => "\\exists"
          })
          print(" " + sort + " " + varName)

          var newCtxt = ctxt pushVar varName

          var sub = subF
          while (sub.isInstanceOf[IQuantified] &&
            sub.asInstanceOf[IQuantified].quan == quan &&
            sub.asInstanceOf[IQuantified].sort == sort) {
            val varName2 = "v" + newCtxt.vars.size
            newCtxt = newCtxt pushVar varName2
            print(", " + varName2)
            val IQuantified(_, newSub) = sub
            sub = newSub
          }

          print("; ")
          TryAgain(sub, newCtxt)
        }

        case ISortedEpsilon(sort, _) => {
          val varName = "v" + ctxt.vars.size
          print("\\eps " + sort + " " + varName + "; ")
          noParentOp(ctxt pushVar varName)
        }
        case INamedPart(name, _) => {
          if (name != PartName.NO_NAME)
            print("\\part[" + name + "] ")
          noParentOp(ctxt)
        }
        case ITrigger(trigs, _) => {
          print("{")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
            yield (ctxt setParentOp ", ")) ++
            List(ctxt setParentOp "} ", ctxt setParentOp ""))
        }
      }
    }

    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)

  }

}
