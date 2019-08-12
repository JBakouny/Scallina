package scala.of.coq.parsercombinators.compiler.customtreehugger

import treehugger.forest._
import definitions._
import treehuggerDSL._
import java.io.PrintWriter
import treehugger.Forest
import treehugger.TreePrinters

trait MyTreePrinters extends TreePrinters { self: Forest =>

  class MyTreePrinter(out: PrintWriter) extends TreePrinter(out) {

    private def symFn[T](tree: Tree, f: Symbol => T, orElse: => T): T = tree.symbol match {
      case null | NoSymbol => orElse
      case sym             => f(sym)
    }
    private def ifSym(tree: Tree, p: Symbol => Boolean) = symFn(tree, p, false)

    import treehugger.api.Modifier
    import Flags._
    override def printTree(tree: Tree) {
      tree match {
        case EmptyTree =>
          print("")

        case classdef: ClassDef if classdef.name == tpnme.ANON_CLASS_NAME =>
          print(classdef.impl)

        case ClassDef(mods, ctormods, name, tparams, vparams, impl) =>
          printlnAnnotations(tree)
          printModifiers(tree, mods)
          val word =
            if (mods.hasTraitFlag) "trait"
            else if (ifSym(tree, _.isModuleClass)) "object"
            else "class"

          print(word, " ", symName(tree, name))
          printTypeParams(tparams)
          if (ctormods != NoMods) {
            print(" ")
            printModifiers(tree, ctormods)
          }
          if (vparams != Nil || modifiersOfFlags(mods.flags).contains(Modifier.`case`))
            printValueParams(vparams, true)

          print(if (mods.isDeferred) " <: "
          else if (impl.parents.isEmpty) ""
          else " extends ", impl)

        case anythingElse => super.printTree(anythingElse)
      }
    }
  }

  override def newTreePrinter(writer: PrintWriter): TreePrinter = new MyTreePrinter(writer)
}

object MyForest extends Forest with MyTreePrinters { self: Forest =>

}
