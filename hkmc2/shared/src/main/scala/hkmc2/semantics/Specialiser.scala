package hkmc2
package semantics

import scala.collection.immutable.Queue
import scala.util.Random

import mlscript.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import hkmc2.semantics.Elaborator.*
import hkmc2.semantics.Split.{Let, Else}
import hkmc2.semantics.Term.*
import hkmc2.syntax.Tree.{Ident, IntLit, StrLit, UnitLit}
import hkmc2.utils.TraceLogger


object Specialiser:
  transparent inline def ctx(using Ctx): Ctx = summon
  transparent inline def state(using Elaborator.State): Elaborator.State = summon
  private transparent inline def wq(using Queue[TermDefinition]): Queue[TermDefinition] = summon

  import hkmc2.semantics.Elaborator.Ctx.Elem

  extension (ctx: Ctx)
    def elem_+(local: Str -> Ctx.Elem): Ctx = ctx.copy(ctx.outer, env = ctx.env + local)
    def map(f: Str -> Ctx.Elem => Str -> Ctx.Elem): Ctx =
      ctx.copy(parent = ctx.parent.map(_.map(f)), env = ctx.env.map(f))
    def showDbg: Str = ctx.env.map((k, v) => s"$k -> ${v}").mkString(", ")

  final case class Binding(val sym: Symbol, val typ: Opt[Ref]) extends Elem:
    def nme: Str = sym.nme
    def symbol: Opt[Symbol] = S(sym)
    def ref(id: Ident)(using Elaborator.State): Term = ??? // TODO: Make own context; this is dumb

  type Ctxl[T] = (Ctx, Queue[TermDefinition]) ?=> T
  type Apps = Map[Str, Ls[Ref]]

class Specialiser(val tl: TraceLogger)(using Raise, Elaborator.State):
  import tl.*
  import Specialiser.*

  private val tInt: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Int"), 0)
  private val tStr: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Str"), 0)
  private val tUnit: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Unit"), 0)

  def block(blk: Blk, apps: Apps): Ctxl[(Blk, Apps)] = trace(s"Specialising block ${blk.showDbg}"):
    @annotation.tailrec
    def go(sts: Ls[Statement], acc: Ls[Statement], apps: Apps): Ctxl[(Blk, Apps)] =
      log(s"Specialising ${sts.headOption.map(_.showDbg).getOrElse("block end. \n")}")
      sts match
        case (b: Blk) :: sts =>
          val (newBlk, lowerApps) = block(b, apps)(using ctx.nest(N), wq)
          go(sts, newBlk :: acc, lowerApps)
        case (t: Term) :: sts =>
          val (newTerm, lowerApps) = term(t, apps)(using ctx.nest(N), wq)
          go(sts, newTerm :: acc, lowerApps)

        case (l: LetDecl) :: sts =>
          ctx.get(l.sym.nme) match
            case S(_) => go(sts, l :: acc, apps)
            case N => go(sts, l :: acc, apps)(using ctx elem_+ l.sym.nme -> Binding(l.sym, N), wq)
        case (d: DefineVar) :: sts =>
          val ntyp: Opt[Ref] = d.rhs match
            case Lit(lit) => lit.asTree match
              case _: IntLit => S(tInt)
              case _: StrLit => S(tStr)
              case _: UnitLit => S(tUnit)
              case _ => N
            case _ => N // TODO: Infer type from other bindings; tuple type inference
          ctx.map((k, v) => if k == d.sym.nme then k -> Binding(d.sym, ntyp) else k -> v).givenIn:
            go(sts, d :: acc, apps)
        case (td: TermDefinition) :: sts => go(sts, td :: acc, apps)(using ctx, wq :+ td)


        case (i: Import) :: sts => go(sts, i :: acc, apps)
        case (md @ ModuleDef(_, sym, _, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)), wq)
          go(sts, md.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pd @ PatternDef(_, sym, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)), wq)
          go(sts, pd.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (p @ ClassDef.Parameterized(_, _, sym, _, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)), wq)
          go(sts, p.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pl @ ClassDef.Plain(_, _, sym, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)), wq)
          go(sts, pl.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (t: TypeLikeDef) :: sts => go(sts, t :: acc, apps)

        case Nil =>
          val (newRes, lowerApps) = term(blk.res, apps)

          log(s"Ctx: ${ctx.showDbg}")
          log(s"Work Queue: ${wq}")
          log(s"Applications: ${lowerApps}")

          val newAcc = wq.foldLeft(acc):
            (sts, td) =>
              val tys = lowerApps.get(td.sym.nme)
              sts ::: tys.getOrElse(Nil).map(ty =>
                Random.setSeed(td.sym.nme.map(_.toInt).product)
                val name = td.sym.nme + "_" + ty.tree.name + "_" + Random.alphanumeric.take(10).mkString
                td.copy(sym = BlockMemberSymbol(name, td.sym.trees))
              )

          (Blk(newAcc.reverse, newRes), lowerApps)

    go(blk.stats, Nil, apps)

  def term(t: Term, apps: Apps): Ctxl[(Term, Apps)] = trace(s"Specialising term ${t.showDbg}"):
    t match
      case app @ App(lhs, rhs) =>
        val name = lhs match
          case SynthSel(_, n) => n.name
          case _ =>
            raise(ErrorReport(msg"I messed up :(" -> t.toLoc :: Nil)) // FIXME
            ""
        val typ: Opt[Ref] = rhs match
          case Tup(fields) => fields.head match // FIXME
            case Fld(_, Lit(lit), _) => lit.asTree match
              case _: IntLit => S(tInt)
              case _: StrLit => S(tStr)
              case _: UnitLit => S(tUnit)
              case _ => N
            case Fld(_, Ref(r), _) => ctx.get(r.nme).flatMap(_.asInstanceOf[Binding].typ)
            case _ => N
          case _ => N

        val newApps = typ match
          case Some(t) => apps + (name -> (t :: apps.getOrElse(name, Nil).filterNot(_.tree == t.tree)))
          case N => apps


        Random.setSeed(name.map(_.toInt).product)
        val s = lhs.asInstanceOf[SynthSel] // FIXME
        val newName: Ident = Ident(name + "_" + typ.map(_.tree.name).getOrElse("oops") + "_" + Random.alphanumeric.take(10).mkString)
        val specApp: App = app.copy(lhs = s.copy(nme = newName)(s.sym))(app.tree, app.resSym)

        (specApp, newApps)
      case il @ IfLike(_, desug) => desug match
        case Let(s, b, t) =>
          val (nb, lowerApps) = term(b, apps)
          (il.copy(desugared = Let(s, nb, t))(il.normalized), lowerApps)
        case Else(d) =>
          val (nd, lowerApps) = term(d, apps)
          (il.copy(desugared = Else(nd))(il.normalized), lowerApps)
        case _ => (il, apps)
      case Lam(params, body) =>
        val (newBody, newApps) = term(body, apps)
        (Lam(params, newBody), newApps)
      case Forall(tvs, body) =>
        val (newTerm, newApps) = term(body, apps)
        (Forall(tvs, newTerm), newApps)
      case Quoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Quoted(newTerm), newApps)
      case Unquoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Unquoted(newTerm), newApps)
      case Region(name, body) =>
        val (newTerm, newApps) = term(body, apps)
        (Region(name, newTerm), newApps)
      case Deref(ref) =>
        val (newTerm, newApps) = term(ref, apps)
        (Deref(newTerm), newApps)
      case Ret(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Ret(newTerm), newApps)
      case Throw(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Throw(newTerm), newApps)
      case Try(body, finallyDo) =>
        val (b1, apps1) = term(body, apps)
        val (b2, apps2) = term(finallyDo, apps1)
        (Try(b1, b2), apps2)
      case b: Blk => block(b, apps)
      case _ => (t, apps) // TODO: Handle the few other term types

  def topLevel(b: Blk): Blk = block(b, Map.empty)(using Ctx.empty, Queue.empty)._1

// class Specialiser(val tl: TraceLogger, val ctx: Ctx)(using val raise: Raise, val state: Elaborator.State):
//   import tl.*
//
//   case class SpApp(sym: Symbol, tys: Map[Symbol, Str], app: App)
//
//   def topLevel(blk: Blk): Ctxl[Blk] = traceNot[Blk](""):
//     val defs = collectDefs(blk)
//     log(s"Functions to specialise: ${defs.keySet}")
//     given Map[Symbol, TermDefinition] = defs
//
//     val (newblk, apps) = collectApps(blk)
//     log(s"Apps to specialise: ${apps}")
//     given Ls[SpApp] = apps
//
//     val newnewblk = generateFunctions(newblk)
//
//     newnewblk
//
//   def collectDefs(term: Term): Ctxl[Map[Symbol, TermDefinition]] = trace(s"Spec term ${term.showDbg}"):
//     term match
//       case Blk(Nil, res) => collectDefs(res)
//       case Blk((d: Declaration) :: stats, res) => collectDefs(Blk(stats, res)) ++ (d match
//         case td@TermDefinition(_, Fun, sym, params, _, Some(body), _, _, _) =>
//           val map = collectDefs(body) ++ collectDefs(Blk(stats, res))
//           if params.flatMap(_.params).exists(_.flags.spec) then map + (td.sym -> td) else map
//         case _ => d.subTerms.foldLeft(Map.empty[Symbol, TermDefinition])((acc, sub) => acc ++ collectDefs(sub)))
//       case Blk((t: Term) :: stats, res) => collectDefs(t) ++ collectDefs(Blk(stats, res))
//       case Blk(LetDecl(_, _) :: stats, res) => collectDefs(Blk(stats, res))
//       case Blk(DefineVar(_, rhs) :: stats, res) => collectDefs(rhs) ++ collectDefs(Blk(stats, res))
//       case _ => term.subTerms.foldLeft(Map.empty)((acc, sub) => acc ++ collectDefs(sub))
//
//   def collectApps(tree: Blk)(using defs: Map[Symbol, TermDefinition], specFns: MutMap[Str, Ident] = MutMap.empty): Ctxl[(Blk, Ls[SpApp])] = trace(s"Collecting term ${tree.showDbg}"):
//     val (stats, types) = tree.stats.foldLeft((Ls.empty[Statement], Ls.empty[SpApp])):
//       (acc, sub) => trace(s"Collecting statement: ${sub.showDbg}"):
//         sub match
//           case t: Term => collectApps(t) match { case (st, ts) => (acc._1 :+ st, acc._2 ::: ts) }
//           case d: DefineVar => collectApps(d.rhs) match { case (st, ts) => (acc._1 :+ d.copy(rhs = st), acc._2 ::: ts) }
//           case td: TermDefinition => td.body match
//             case S(t) => collectApps(t) match { case (st, ts) => (acc._1 :+ td.copy(body = S(st)), acc._2 ::: ts) }
//             case N => (acc._1 :+ td, acc._2)
//           // TODO: Other non term statements
//           case s => (acc._1 :+ s, acc._2)
//     collectApps(tree.res) match { case (res, ts) => (Blk(stats, res), types ::: ts) }
//
//   def collectApps(tree: Term)(using defs: Map[Symbol, TermDefinition], specFns: MutMap[Str, Ident]): Ctxl[(Term, Ls[SpApp])] =
//     trace(s"Collecting term ${tree.showDbg}"):
//       tree match
//         case app@App(lhs, Tup(fields)) => lhs match
//           case s@Sel(pre, nme) =>
//             log(s"Def: ${s.sym.map(os => ctx.get(os.nme))}")
//             if s.sym.isDefined && defs.contains(s.sym.get) then
//               val typs = defs(s.sym.get).params.flatMap(_.params).zip(fields.filter(e => e.isInstanceOf[Fld]).map(_.asInstanceOf[Fld].term).map {
//                 case Lit(lit) => lit.asTree match
//                   case _: IntLit => "Int"
//                   case _: StrLit => "Str"
//                   case _ => ""
//                 case _ => "Any"
//               }).filter(_._1.flags.spec)
//               log(s"Specialising ${s.sym.get} with ${typs.map((s, t) => s.sym.nme + ": " + t)}.")
//               val fId = s.sym.get.nme + typs.map(_._2).mkString("_", "_", "")
//               val name = specFns.getOrElseUpdate(fId, Ident(fId + "_" + state.suid.nextUid))
//               val specApp: App = app.copy(lhs = s.copy(nme = name)(s.sym))(app.tree, app.resSym)
//               (specApp, SpApp(s.sym.get, typs.foldLeft(Map.empty)((acc, p) => acc + (p._1.sym -> p._2)), specApp) :: Nil)
//             else
//               (tree, Nil)
//           // FIXME: Ref applications aren't implemented, nor do I know when they are used
//           case Ref(sym) => if defs.contains(sym) then (tree, SpApp(TempSymbol(N, ""), Map.empty, app) :: Nil) else (tree, Nil)
//           case _ => (tree, Nil)
//         case b: Blk => collectApps(b)
//         // FIXME: This won't work for nested applications in all cases
//         case _ => tree.subTerms.foldLeft((tree, Nil))((acc, sub) => (acc._1, collectApps(sub)._2 ::: acc._2))
//
//   def generateFunctions(tree: Blk)(using defs: Map[Symbol, TermDefinition], apps: Ls[SpApp]): Ctxl[Blk] =
//     val uniqueApps = apps.groupBy(_.sym).map((k, v) => (defs(k), v.groupBy(_.tys.toSet).map(_._2.head).map(a => (a.app, a.tys))))
//     given Map[TermDefinition, Iterable[(App, Map[Symbol, Str])]] = uniqueApps
//     log(s"Generating functions for: ${uniqueApps}")
//     Blk(tree.stats, tree.res)
//     // val tmp = uniqueApps.foldLeft(tree.stats)((acc, app) =>
//     //   val (defn, tys) = app
//     //   tys.map(ty =>
//     //     defn.copy(
//     //       sym = BlockMemberSymbol(ty._1.lhs.asInstanceOf[Sel].nme.name, Nil),
//     //       params = defn.params.map(pl =>
//     //         pl.copy(params = pl.params.map(p =>
//     //           ty._2.get(p.sym) match
//     //             case S(t) => p.copy(sign = S(Sel(Ref(TopLevelSymbol("import#Prelude"))(Ident(""), 0), Ident(t))(N)))
//     //             case _ => p
//     //         ))
//     //       )
//     //     )
//     //   ).toList :::
//     // )
//     // Blk(tmp, tree.res)
//