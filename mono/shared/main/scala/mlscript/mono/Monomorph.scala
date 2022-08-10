package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.{AppliedType, TypeName}
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, If}
import mlscript.{IfTerm, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import scala.collection.immutable.{HashMap}
import scala.collection.mutable.{Map as MutMap, Set as MutSet}
import scala.collection.mutable.ArrayBuffer
import mlscript.Cls
import mlscript.CaseBranches
import mlscript.TypeDefKind
import mlscript.AppliedType.apply
import mlscript.mono.specializer.Builtin

import mlscript.mono.printer.ExprPrinter

class Monomorph(debugMode: Boolean):
  private val debug = if debugMode then RainbowDebug() else DummyDebug()

  import Helpers._
  import Monomorph._

  /**
   * Specialized implementations of function declarations.
   */
  private val funImpls = MutMap[String, (Item.FuncDecl, MutMap[String, Item.FuncDecl])]()
  private def allFunImpls: IterableOnce[(Item.FuncDecl, Item.FuncDecl)] =
    funImpls.iterator.flatMap { case (name, (protoFunc, implFunc)) =>
      implFunc.values.map((protoFunc, _))
    }

  /**
   * Specialized implementations of each type declarations.
   */
  private val tyImpls = MutMap[String, SpecializationMap[Item.TypeDecl]]()
  /**
   * Add a prototype type declaration.
   */
  private def addPrototypeTypeDecl(typeDecl: Item.TypeDecl) =
    tyImpls.addOne(typeDecl.name.name, SpecializationMap(typeDecl))
  /**
   * An iterator going through all type declarations.
   */
  private def allTypeDecls: IterableOnce[Item.TypeDecl] =
    tyImpls.values.flatMap { _.iterator }

  /**
   * A global store of monomorphized lambda classes.
   */
  private val lamTyDefs = MutMap[String, Item.TypeDecl]()
  /**
   * A global store of anonymous classes. For example, `new { ... }`.
   */
  private val anonymTyDefs = MutMap[String, Item.TypeDecl]()

  /**
   * This function monomorphizes the top-level `TypingUnit` into a `Module`.
   */
  def monomorphize(tu: TypingUnit): Module =
    debug.trace("MONO MODL", PrettyPrinter.show(tu)) {
      mlscript.mono.Module(tu.entities.iterator.flatMap[Expr | Item] {
        case Left(term) =>
          Some(monomorphizeTerm(term))
        case Right(tyDef: NuTypeDef) => 
          monomorphizeTypeDef(tyDef)
          None
        case Right(funDef: NuFunDef) =>
          val funcItem = monomorphizeFunDef(funDef)
          funcItem match
            case funcDecl: Item.FuncDecl =>
              funImpls.addOne(funcDecl.name.name, (funcDecl, MutMap()))
            case _ => ()
          Some(funcItem)
      }.concat(allFunImpls.map(_._2))
       .concat(allTypeDecls)
       .concat(lamTyDefs.values)
       .concat(anonymTyDefs.values)
       .toList)
    }(ExprPrinter.print)

  /**
   * This function monomorphizes the nested `TypingUnit` into a `Isolation`.
   */
  def monomorphizeBody(body: TypingUnit): Isolation =
    debug.trace("MONO BODY", PrettyPrinter.show(body)) {
      Isolation(body.entities.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
        case Left(term) =>
          Some(monomorphizeTerm(term))
        case Right(tyDef: NuTypeDef) => 
          monomorphizeTypeDef(tyDef)
          None
        case Right(funDef: NuFunDef) =>
          Some(monomorphizeFunDef(funDef))
      })
    }(ExprPrinter.print)

  /**
   * This function flattens a top-level type definition and returns the root
   * type definition. There is a simple class lifting here.
   */
  private def monomorphizeTypeDef(tyDef: NuTypeDef): Item.TypeDecl =
    debug.trace("MONO TDEF", PrettyPrinter.show(tyDef)) {
      /**
       * The recursive function doing the real work.
       * @param tyDef the type definition
       * @param namePath enclosing class names and this class name
       */
      def rec(tyDef: NuTypeDef, namePath: List[String]): Item.TypeDecl =
        debug.trace[Item.TypeDecl]("LIFT", PrettyPrinter.show(tyDef)) {
          val NuTypeDef(kind, _, tparams, params, parents, body) = tyDef
          val isolation = Isolation(body.entities.flatMap {
            // Question: Will there be pure terms in class body?
            case Left(term) =>
              Some(monomorphizeTerm(term))
            case Right(subTypeDef: NuTypeDef) =>
              rec(subTypeDef, subTypeDef.nme.name :: namePath)
              None
            case Right(subFunDef: NuFunDef) =>
              Some(monomorphizeFunDef(subFunDef))
          })
          val className = namePath.reverseIterator.mkString("_")
          val typeDecl: Item.TypeDecl = Item.TypeDecl(
            className,
            kind,
            tparams,
            toFuncParams(params).toList,
            parents,
            isolation
          )
          addPrototypeTypeDecl(typeDecl)
          typeDecl
        }()

      rec(tyDef, tyDef.nme.name :: Nil)
    }(ExprPrinter.print)
    
  /**
   * This function monomorphizes a function definition in smoe typing units.
   * @param tyDecls the destination of nested type declarations
   */
  private def monomorphizeFunDef(funDef: NuFunDef): Item.FuncDecl | Item.FuncDefn =
    debug.trace[Item.FuncDecl | Item.FuncDefn]("MONO FUNC", PrettyPrinter.show(funDef)) {
      val NuFunDef(nme, targs, rhs) = funDef
      rhs match
        case Left(Lam(params, body)) =>
          Item.FuncDecl(nme, toFuncParams(params).toList, monomorphizeTerm(body))
        case Left(body) => Item.FuncDecl(nme, Nil, monomorphizeTerm(body))
        case Right(polyType) => Item.FuncDefn(nme, targs, polyType)
    }(ExprPrinter.print)

  /**
   * This function monomophizes a `Term` into an `Expr`.
   */
  def monomorphizeTerm(term: Term): Expr =
    debug.trace[Expr]("MONO TERM", PrettyPrinter.show(term)) {
      term match
        case Var(name) => Expr.Ref(name)
        case Lam(lhs, rhs) => monomorphizeLambda(lhs, rhs)
        case App(App(Var("=>"), Bra(false, args: Tup)), body) =>
          monomorphizeLambda(args, body)
        case App(lhs, rhs) =>
          val callee = monomorphizeTerm(lhs)
          val arguments = toFuncArgs(rhs).map(monomorphizeTerm).toList
          callee match
            case Expr.Ref(name) =>
              specializeCall(name, arguments).fold(Expr.Apply(callee, arguments))(identity)
            case _ => Expr.Apply(callee, arguments)
        case Tup(fields) =>
          Expr.Tuple(fields.map {
            case (_, Fld(mut, spec, value)) => monomorphizeTerm(value)
          })
        case Rcd(fields) =>
          Expr.Record(fields.map {
            case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(value))
          })
        case Sel(receiver, fieldName) =>
          Expr.Select(monomorphizeTerm(receiver), fieldName)
        case Let(isRec, name, rhs, body) =>
          Expr.LetIn(isRec, name, monomorphizeTerm(rhs), monomorphizeTerm(body))
        case Blk(stmts) => Expr.Block(stmts.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
          case term: Term => Some(monomorphizeTerm(term))
          case tyDef: NuTypeDef =>
            monomorphizeTypeDef(tyDef)
            None
          case funDef: NuFunDef => Some(monomorphizeFunDef(funDef))
          case mlscript.DataDefn(_) => throw MonomorphError("unsupported DataDefn")
          case mlscript.DatatypeDefn(_, _) => throw MonomorphError("unsupported DatatypeDefn")
          case mlscript.TypeDef(_, _, _, _, _, _) => throw MonomorphError("unsupported TypeDef")
          case mlscript.Def(_, _, _) => throw MonomorphError("unsupported Def")
          case mlscript.LetS(_, _, _) => throw MonomorphError("unsupported LetS")
        })
        case Bra(rcd, term) => monomorphizeTerm(term)
        case Asc(term, ty) => Expr.As(monomorphizeTerm(term), ty)
        case _: Bind => throw MonomorphError("cannot monomorphize `Bind`")
        case _: Test => throw MonomorphError("cannot monomorphize `Test`")
        case With(term, Rcd(fields)) =>
          Expr.With(monomorphizeTerm(term), Expr.Record(fields.map {
            case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(term))
          }))
        case CaseOf(term, cases) => ???
        case Subs(array, index) =>
          Expr.Subscript(monomorphizeTerm(array), monomorphizeTerm(index))
        case Assign(lhs, rhs) =>
          Expr.Assign(monomorphizeTerm(lhs), monomorphizeTerm(rhs))
        case New(None, body) =>
          val className = s"Anonym_${anonymTyDefs.size}"
          val classDecl = Item.classDecl(className, Nil, monomorphizeBody(body))
          Expr.Apply(className, Nil)
        case New(Some((constructor, args)), body) =>
          val typeName = constructor match
            case AppliedType(TypeName(name), _) => name
            case TypeName(name)                 => name
          specializeNew(typeName, toFuncArgs(args).toList, body)
        case Block(unit) => Expr.Isolated(monomorphizeBody(unit))
        case If(body, alternate) => body match
          case term: IfTerm => throw MonomorphError("unsupported IfTerm")
          case IfThen(condition, consequent) =>
            Expr.IfThenElse(
              monomorphizeTerm(condition),
              monomorphizeTerm(consequent),
              alternate.map(monomorphizeTerm)
            )
          case term: IfElse => throw MonomorphError("unsupported IfElse")
          case term: IfLet => throw MonomorphError("unsupported IfLet")
          case term: IfOpApp => throw MonomorphError("unsupported IfOpApp")
          case term: IfOpsApp => throw MonomorphError("unsupported IfOpsApp")
          case term: IfBlock => throw MonomorphError("unsupported IfBlock")
        case IntLit(value) => Expr.Literal(value)
        case DecLit(value) => Expr.Literal(value)
        case StrLit(value) => Expr.Literal(value)
        case UnitLit(undefinedOrNull) => 
          Expr.Literal(if undefinedOrNull
                       then UnitValue.Undefined
                       else UnitValue.Null)
    }(ExprPrinter.print)

  def monomorphizeLambda(args: Term, body: Term): Expr =
    debug.trace("MONO LAMBDA", args.toString + " => " + body) {
      val params = toFuncParams(args).toList
      // TODO: Capture variables referenced in the lambda body.
      // We should capture: closure variables and referenced type variables.
      val className = s"Lambda_${lamTyDefs.size}"
      val applyMethod: Item.FuncDecl =
        Item.FuncDecl("apply", toFuncParams(args).toList, monomorphizeTerm(body))
      val classBody = Isolation(applyMethod :: Nil)
      val classDecl = Item.classDecl(className, Nil, classBody)
      // Add to the global store.
      lamTyDefs.addOne((className, classDecl))
      // Returns a class construction.
      Expr.Apply(Expr.Ref(className), Nil)
    }(ExprPrinter.print)

  /**
   * `new C(...) { ... }` expressions are converted into
   * `{ class CImpl extends C(...) { ... }; CImpl() }`.
   * ~~This requires you to add a `LetClass` construct to `mlscript.Term`.~~
   */
  def specializeNew(name: String, termArgs: List[Term], termBody: TypingUnit): Expr.Apply =
    debug.trace[Expr.Apply]("SPEC NEW", {
      name + termArgs.iterator.map(_.toString).mkString("(", ", ", ")") +
        " with " + PrettyPrinter.show(termBody)
    }) {
      val args = termArgs.map(monomorphizeTerm)
      val body = monomorphizeBody(termBody)
      val specTypeDecl = specializeTypeDef(name, args, body)
      Expr.Apply(specTypeDecl.name, Nil)
    }(ExprPrinter.print)

  def specializeCall(name: String, args: List[Expr]): Option[Expr] =
    debug.trace("SPEC CALL", name + args.mkString("(", ", ", ")")) {
      if tyImpls.contains(name) then specializeClassCall(name, args)
      else if funImpls.contains(name) then specializeFunctionCall(name, args)
      else None
    }()

  private def partitationArguments(params: List[Parameter], args: List[Expr]): (List[Expr], List[Expr]) =
    if (args.length != params.length) {
      throw MonomorphError(s"expect ${params.length} arguments but ${args.length} were given")
    }
    val staticArguments = params.iterator.zip(args).flatMap({
      case ((true, _), value) => Some(value)
      case _ => None
    }).toList
    val dynamicArguments = params.iterator.zip(args).flatMap({
      case ((false, _), value) => Some(value)
      case _ => None
    }).toList
    (staticArguments, dynamicArguments)

  private def generateSignature(staticArguments: List[Expr]): String =
    staticArguments.iterator.map(DataType.infer(_, None)).mkString("__", "_", "")

  def specializeClassCall(name: String, args: List[Expr]): Option[Expr] =
    debug.trace("SPEC CLASS CALL", name + args.mkString("(", ", ", ")")) {
      import TypeDeclKind._
      tyImpls.get(name).flatMap { specClassMap => specClassMap.prototype match
        case Item.TypeDecl(Expr.Ref(name), Class, typeParams, params, parents, body) =>
          val (staticArguments, dynamicArguments) = partitationArguments(params, args)
          if (staticArguments.isEmpty) {
            None
          } else {
            val signature = generateSignature(staticArguments)
            val specClassDecl = specClassMap.getOrInsert(signature, {
              specClassMap.base = Item.TypeDecl(
                Expr.Ref(s"${name}" + signature), // name
                Class, // kind
                typeParams, // typeParams
                Nil, // params
                Nil, // parents
                Isolation.empty // body
              )
              val values = params.iterator.zip(args).flatMap({
                case ((true, Expr.Ref(name)), value) => Some((name, value))
                case ((false, _), _) => None
              })
              Item.TypeDecl(
                Expr.Ref(s"${name}" + signature), // name
                Class, // kind
                typeParams, // typeParams
                params.filter(!_._1), // params
                TypeName(name) :: Nil, // parents
                specializeClass(specClassMap.prototype)(using HashMap.from(values)) // body
              )
            })
            Some(Expr.Apply(specClassDecl.name, dynamicArguments))
          }
        case Item.TypeDecl(_, Trait, _, _, _, _) =>
          throw new MonomorphError(s"cannot specialize trait $name")
        case Item.TypeDecl(_, Alias, _, _, _, _) =>
          throw new MonomorphError(s"cannot specialize type alias $name")
      }
    }(_.fold("<none>")(ExprPrinter.print))

  // TODO: Remove `Option[Expr]` by passing the callee.
  def specializeFunctionCall(name: String, args: List[Expr]): Option[Expr] =
    debug.trace("SPEC FUNC CALL", name + args.mkString("(", ", ", ")")) {
      funImpls.get(name).flatMap { case (Item.FuncDecl(ref, params, body), impls) =>
        val (staticArguments, dynamicArguments) = partitationArguments(params, args)
        if (staticArguments.isEmpty) {
          None
        } else {
          val signature = generateSignature(staticArguments)
          val specFuncDecl = impls.get(signature).getOrElse[Item.FuncDecl] {
            val values = params.iterator.zip(args).flatMap({
              case ((true, Expr.Ref(name)), value) => Some((name, value))
              case ((false, _), _) => None
            })
            val specFuncBody = specializeExpr(body)(using HashMap.from(values))
            val staticParams = params.filter(!_._1)
            val specFuncName = s"${name}" + signature
            val funcDecl: Item.FuncDecl = Item.FuncDecl(specFuncName, staticParams, specFuncBody)
            impls.addOne((specFuncName, funcDecl))
            funcDecl
          }
          Some(Expr.Apply(specFuncDecl.name, dynamicArguments))
        }
      }
    }(_.fold("<none>")(ExprPrinter.print))

  private def showInContext(content: String)(using ctx: HashMap[String, Expr]): String = 
    content + " in context " + (if ctx.isEmpty then "{}" else ctx.mkString("{\n  ", "\n  ", "\n}"))

  def specializeExpr(expr: Expr)(using ctx: HashMap[String, Expr]): Expr =
    debug.trace[Expr]("SPEC EXPR", showInContext(expr.toString)) {
      expr match
        case Expr.Ref(name) => ctx.get(name) match
          case Some(value) => value
          case None => expr
        case _: Expr.Lambda => expr
        case Expr.Apply(Expr.Apply(ident @ Expr.Ref(name), lhsExpr :: Nil), rhsExpr :: Nil)
            if Builtin.isBinaryOperator(name) =>
          val lhs = specializeExpr(lhsExpr)
          val rhs = specializeExpr(rhsExpr)
          Builtin.evalulateBinaryOperation(name, lhs, rhs)
            .getOrElse(Expr.Apply(Expr.Apply(ident, lhs :: Nil), rhs :: Nil))
        case Expr.Apply(callee, arguments) =>
          val specCallee = specializeExpr(callee)
          val specArgs = arguments.map(specializeExpr)
          specCallee match
            case Expr.Ref(name) => specializeCall(name, specArgs).getOrElse(expr)
            case Expr.Lambda(params, body) =>
              // Same as `specializeFuncDecl` but I should extract some common stuffs.
              ???
            case other => throw MonomorphError(s"not a callable: $other")
        case Expr.Tuple(elements) => Expr.Tuple(elements.map(specializeExpr))
        case Expr.Record(fields) => Expr.Record(fields.map {
          case (key, value) => (key, specializeExpr(value))
        })
        case Expr.Select(receiver, field) =>
          // We can do more.
          Expr.Select(specializeExpr(receiver), field)
        case Expr.LetIn(true, name, Expr.Lambda(params, body), cont) =>
          // Create a callable entry in the context and recursively specialize
          // the continuation.
          ???
        case Expr.LetIn(true, _, _, _) =>
          throw MonomorphError(s"recursive non-function definition are not allowed")
        case Expr.LetIn(false, Expr.Ref(name), rhs, body) =>
          val specRhs = specializeExpr(rhs)
          specializeExpr(body)(using ctx + (name -> specRhs))
        case Expr.Block(items) =>
          val onlyExpressions = items.iterator.flatMap {
            case expr: Expr => Some(expr)
            case _ => None
          }
          onlyExpressions.map(specializeExpr).toList match
            case Nil => Expr.Literal(UnitValue.Undefined)
            case items => items.last
        case expr: Expr.Literal => expr
        case Expr.IfThenElse(condition, consequent, alternate) =>
          specializeExpr(
            if specializeExpr(condition).asBoolean()
            then consequent
            else alternate.getOrElse(Expr.Literal(UnitValue.Undefined))
          )
        case _ => throw MonomorphError(s"unimplemented ${expr.getClass()}")
    }(ExprPrinter.print)

  /**
   * This function monomorphizes the given class with given arguments.
   * @return specialized class name and all included classes
   */
  def specializeTypeDef(
      name: String,
      args: List[Expr],
      body: Isolation
  ): Item.TypeDecl =
    debug.trace[Item.TypeDecl]("SPEC TDEF", name + args.mkString("(", ", ", ")") + " {\n" + body + "\n}") {
      tyImpls.get(name) match {
        case Some(classSpecMap) =>
          val Item.TypeDecl(_, kind, typeParams, params, parents, body) = classSpecMap.prototype
          val implClassName: Expr.Ref = Expr.Ref(s"${name}_${classSpecMap.size}")
          Item.TypeDecl(implClassName, kind, typeParams, params, parents, body)
          // FIXME: Logic here does not work.
        case None => throw new MonomorphError(s"cannot specialize undeclared type $name")
      }
    }(ExprPrinter.print)

  def specializeFunction(funcProto: Item.FuncDecl)(using ctx: HashMap[String, Expr]): Item.FuncDecl =
    Item.FuncDecl(funcProto.name, funcProto.params, specializeExpr(funcProto.body))

  def specializeClass(classProto: Item.TypeDecl)(using ctx: HashMap[String, Expr]): Isolation =
    debug.trace("SPEC CLASS", showInContext(s"class ${classProto.name.name}")) {
      Isolation(classProto.body.items.map {
        case expr: Expr => specializeExpr(expr)
        case funcDecl: Item.FuncDecl => specializeFunction(funcDecl)
        case other => throw MonomorphError(s"$other is not supported")
      })
    }(ExprPrinter.print)

  // Shorthand implicit conversions.

  private given Conversion[String, Expr.Ref] with
    def apply(name: String): Expr.Ref = Expr.Ref(name)

  private given Conversion[Var, Expr.Ref] with
    def apply(nme: Var): Expr.Ref = Expr.Ref(nme.name)

  private given Conversion[TypeName, Expr.Ref] with
    def apply(nme: TypeName): Expr.Ref = Expr.Ref(nme.name)

  private given Conversion[TypeDefKind, TypeDeclKind] with
    import mlscript.{Als, Cls, Trt}
    def apply(kind: TypeDefKind): TypeDeclKind = kind match
      case Als => TypeDeclKind.Alias
      case Cls => TypeDeclKind.Class
      case Trt => TypeDeclKind.Trait

object Monomorph:
  class SpecializationMap[T <: Item](val prototype: T):
    private var basePrototype: Option[T] = None
    private val implementations = MutMap[String, T]()

    inline def getOrInsert(signature: String, op: => T): T =
      implementations.getOrElseUpdate(signature, op)
    inline def size: Int = implementations.size
    // signature + item
    inline def +=(entry: (String, T)): T =
      implementations.addOne(entry)
      entry._2
    inline def base: Option[T] = basePrototype
    inline def base_=(op: => T): Unit =
      basePrototype match 
        case None => basePrototype = Some(op)
        case Some(_) => ()
    inline def isEmpty: Boolean = implementations.isEmpty
    inline def iterator: Iterator[T] =
      if implementations.isEmpty then Iterator.empty else
        basePrototype.iterator.concat(implementations.values)