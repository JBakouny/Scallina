package scala.of.coq.parsercombinators.compiler

import treehugger.forest._
import treehuggerDSL._

trait CurryingStrategy {
  def createApplication(functionTerm: Tree, arguments: List[Tree]): Tree
  def createDefinition(functionDef: DefTreeStart, paramDefs: List[ValDef]): DefTreeStart
  def createAnonymousFunction(paramDefs: List[ValDef], bodyTerm: Tree): Tree
  def createCompanionObject(name: String, typeDefs: List[TypeDefTreeStart], paramDefs: List[ValDef]): Option[ModuleDef]
}

object Currify extends CurryingStrategy {
  def createApplication(functionTerm: Tree, arguments: List[Tree]): Tree = {
    arguments.foldLeft(functionTerm)(
      (f, param) => f.APPLY(param)
    )
  }
  def createDefinition(functionDef: DefTreeStart, paramDefs: List[ValDef]): DefTreeStart = {
    paramDefs.foldLeft(functionDef)(
      (funDef, param) => funDef.withParams(param)
    )
  }
  def createAnonymousFunction(paramDefs: List[ValDef], bodyTerm: Tree): Tree = {
    paramDefs.foldRight(bodyTerm)(
      (param, bodyTerm) => LAMBDA(param) ==> bodyTerm
    )
  }

  def createCompanionObject(
      name: String,
      typeDefs: List[TypeDefTreeStart],
      paramDefs: List[ValDef]
  ): Option[ModuleDef] = {
    def callClassConstructor(name: String, paramDefs: List[ValDef]) = {
      NEW(
        name,
        paramDefs.map { param =>
          REF(param.name)
        }: _*
      )
    }

    def createApplyMethodBody(name: String, paramDefs: List[ValDef]) = {
      createAnonymousFunction(
        paramDefs,
        callClassConstructor(name, paramDefs)
      )
    }

    if (paramDefs.size <= 1) {
      None
    } else {
      Some(
        OBJECTDEF(name) :=
          BLOCK(
            DEF("apply").withTypeParams(typeDefs) :=
              createApplyMethodBody(
                name,
                paramDefs
              )
          )
      )
    }
  }
}

object NoCurrying extends CurryingStrategy {
  def createApplication(functionTerm: Tree, arguments: List[Tree]): Tree = {
    functionTerm.APPLY(arguments)
  }
  def createDefinition(functionDef: DefTreeStart, paramDefs: List[ValDef]): DefTreeStart = {
    functionDef.withParams(paramDefs)
  }
  def createAnonymousFunction(paramDefs: List[ValDef], bodyTerm: Tree): Tree = {
    LAMBDA(paramDefs) ==> bodyTerm
  }
  def createCompanionObject(
      name: String,
      typeDefs: List[TypeDefTreeStart],
      paramDefs: List[ValDef]
  ): Option[ModuleDef] = None
}
