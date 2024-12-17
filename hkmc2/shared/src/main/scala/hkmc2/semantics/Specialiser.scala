package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import hkmc2.semantics.Elaborator.*
import hkmc2.semantics.Term.*
import hkmc2.syntax.Fun
import hkmc2.syntax.Tree.{Ident, IntLit, StrLit}
import hkmc2.utils.TraceLogger

import scala.collection.mutable.{Map => MutMap}


/* TODO:
 *   - Handle curried functions & partial applications
 */

class Specialiser(val tl: TraceLogger, val ctx: Ctx)(using val raise: Raise, val state: Elaborator.State):
  import tl.*
  
  case class SpApp(sym: Symbol, tys: Map[Symbol, Str], app: App)
  
  def topLevel(blk: Blk): Ctxl[Blk] = traceNot[Blk](""):
    val defs = collectDefs(blk)
    log(s"Functions to specialise: ${defs.keySet}")
    given Map[Symbol, TermDefinition] = defs
    
    val (newblk, apps) = collectApps(blk)
    log(s"Apps to specialise: ${apps}")
    given Ls[SpApp] = apps
    
    val newnewblk = generateFunctions(newblk)
    
    newnewblk
  
  def collectDefs(term: Term): Ctxl[Map[Symbol, TermDefinition]] = trace(s"Spec term ${term.showDbg}"):
    term match
      case Blk(Nil, res) => collectDefs(res)
      case Blk((d: Declaration) :: stats, res) => collectDefs(Blk(stats, res)) ++ (d match
        case td@TermDefinition(_, Fun, sym, params, _, Some(body), _) =>
          val map = collectDefs(body) ++ collectDefs(Blk(stats, res))
          if params.flatMap(_.params).exists(_.flags.spec) then map + (td.sym -> td) else map
        case _ => d.subTerms.foldLeft(Map.empty[Symbol, TermDefinition])((acc, sub) => acc ++ collectDefs(sub)))
      case Blk((t: Term) :: stats, res) => collectDefs(t) ++ collectDefs(Blk(stats, res))
      case Blk(LetDecl(_) :: stats, res) => collectDefs(Blk(stats, res))
      case Blk(DefineVar(_, rhs) :: stats, res) => collectDefs(rhs) ++ collectDefs(Blk(stats, res))
      case _ => term.subTerms.foldLeft(Map.empty)((acc, sub) => acc ++ collectDefs(sub))
  
  def collectApps(tree: Blk)(using defs: Map[Symbol, TermDefinition], specFns: MutMap[Str, Ident] = MutMap.empty): Ctxl[(Blk, Ls[SpApp])] = trace(s"Collecting term ${tree.showDbg}"):
    val (stats, types) = tree.stats.foldLeft((Ls.empty[Statement], Ls.empty[SpApp])):
      (acc, sub) => trace(s"Collecting statement: ${sub.showDbg}"):
        sub match
          case t: Term => collectApps(t) match { case (st, ts) => (acc._1 :+ st, acc._2 ::: ts) }
          case d: DefineVar => collectApps(d.rhs) match { case (st, ts) => (acc._1 :+ d.copy(rhs = st), acc._2 ::: ts) }
          case td: TermDefinition => td.body match
            case S(t) => collectApps(t) match { case (st, ts) => (acc._1 :+ td.copy(body = S(st)), acc._2 ::: ts) }
            case N => (acc._1 :+ td, acc._2)
          // TODO: Other non term statements
          case s => (acc._1 :+ s, acc._2)
    collectApps(tree.res) match { case (res, ts) => (Blk(stats, res), types ::: ts) }
  
  // TODO: Make specFns immutable so this can be nice and pure
  def collectApps(tree: Term)(using defs: Map[Symbol, TermDefinition], specFns: MutMap[Str, Ident]): Ctxl[(Term, Ls[SpApp])] =
    trace(s"Collecting term ${tree.showDbg}"):
      tree match
        case app@App(lhs, Tup(fields)) => lhs match
          case s@Sel(pre, nme) =>
            if s.sym.isDefined && defs.contains(s.sym.get) then
              val typs = defs(s.sym.get).params.flatMap(_.params).zip(fields.map(_.value).map {
                case Lit(lit) => lit.asTree match
                  case _: IntLit => "Int"
                  case _: StrLit => "Str"
                  case _ => ""
                case _ => "Any"
              }).filter(_._1.flags.spec)
              log(s"Specialising ${s.sym.get} with ${typs.map((s, t) => s.sym.nme + ": " + t)}.")
              val fId = s.sym.get.nme + typs.map(_._2).mkString("_", "_", "")
              val name = specFns.getOrElseUpdate(fId, Ident(fId + "_" + state.nextUid)) // not sure state is the way to do this
              val specApp: App = app.copy(lhs = s.copy(nme = name)(s.sym))(app.tree, app.resSym)
              (specApp, SpApp(s.sym.get, typs.foldLeft(Map.empty)((acc, p) => acc + (p._1.sym -> p._2)), specApp) :: Nil)
            else
              (tree, Nil)
          // FIXME: Ref applications aren't implemented, nor do I know when they are used
          case Ref(sym) => if defs.contains(sym) then (tree, SpApp(TempSymbol(999, N, ""), Map.empty, app) :: Nil) else (tree, Nil)
          case _ => (tree, Nil)
        case b: Blk => collectApps(b)
        // FIXME: This won't work for nested applications in all cases
        case _ => tree.subTerms.foldLeft((tree, Nil))((acc, sub) => (acc._1, collectApps(sub)._2 ::: acc._2))
  
  def generateFunctions(tree: Blk)(using defs: Map[Symbol, TermDefinition], apps: Ls[SpApp]): Ctxl[Blk] =
    val uniqueApps = apps.groupBy(_.sym).map((k, v) => (k, v.groupBy(_.tys.toSet).map(_._2.head).map(a => (a.app, a.tys))))
    log(s"Generating functions for: ${uniqueApps}")
    val tmp = uniqueApps.foldLeft(tree.stats)((acc, app) =>
      val (fun, tys) = app
      val defn = defs(fun)
      tys.map(ty =>
        defn.copy(
          sym = BlockMemberSymbol(ty._1.lhs.asInstanceOf[Sel].nme.name, Nil),
          params = defn.params.map(pl =>
            pl.copy(params = pl.params.map(p =>
              ty._2.get(p.sym) match
                // TODO: I don't know what the second and third parameter of ref do
                case S(t) => p.copy(sign = S(Sel(Ref(TopLevelSymbol("import#Prelude"))(Ident(""), 0), Ident(t))(N)))
                case _ => p
            ))
          )
        )
      ).toList ::: acc
    )
    Blk(tmp, tree.res)
