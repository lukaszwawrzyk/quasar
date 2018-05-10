/*
 * Copyright 2014–2018 SlamData Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package quasar.qscript.rewrites

import slamdata.Predef.{Map => _, _}
import quasar.RenderTreeT
import quasar.contrib.pathy.{ADir, AFile}
import quasar.contrib.matryoshka._
import quasar.ejson.implicits._
import quasar.fp._
import quasar.fp.ski._
import quasar.qscript._
import quasar.qscript.RecFreeS._
import quasar.qscript.MapFuncCore._
import quasar.qscript.MapFuncsCore._

import matryoshka.{Hole => _, _}
import matryoshka.data._
import matryoshka.implicits._
import matryoshka.patterns._
import scalaz._, Scalaz._
import iotaz.{CopK, TListK}

/** Rewrites adjacent nodes. */
trait Coalesce[X[_]] {
  type IT[F[_]]

  /** Coalesce for types containing QScriptCore. */
  protected[qscript] def coalesceQC[F[_]: Functor]
    (FToOut: PrismNT[F, X])
      : X[IT[F]] => Option[X[IT[F]]]

  def coalesceQCNormalize[F[_]: Functor]
    (FToOut: PrismNT[F, X])
    (implicit N: Normalizable[X])
      : X[IT[F]] => Option[X[IT[F]]] =
    applyTransforms(coalesceQC[F](FToOut), N.normalizeF(_: X[IT[F]]))

  /** Coalesce for types containing ShiftedRead. */
  protected[qscript] def coalesceSR[F[_]: Functor, A]
    (FToOut: PrismNT[F, X])
      : X[IT[F]] => Option[X[IT[F]]]

  def coalesceSRNormalize[F[_]: Functor, A]
    (FToOut: PrismNT[F, X])
    (implicit N: Normalizable[X])
      : X[IT[F]] => Option[X[IT[F]]] =
    applyTransforms(coalesceSR[F, A](FToOut), N.normalizeF(_: X[IT[F]]))

  /** Coalesce for types containing EquiJoin. */
  protected[qscript] def coalesceEJ[F[_]: Functor]
    (FToOut: F ~> λ[α => Option[X[α]]])
      : X[IT[F]] => Option[X[IT[F]]]

  def coalesceEJNormalize[F[_]: Functor]
    (FToOut: F ~> λ[α => Option[X[α]]])
    (implicit N: Normalizable[X])
      : X[IT[F]] => Option[X[IT[F]]] = in => {
    coalesceEJ[F](FToOut).apply(in).flatMap(N.normalizeF(_: X[IT[F]]))
  }

  /** Coalesce for types containing ThetaJoin. */
  protected[qscript] def coalesceTJ[F[_]: Functor]
    (FToOut: F ~> λ[α => Option[X[α]]])
      : X[IT[F]] => Option[X[IT[F]]]

  def coalesceTJNormalize[F[_]: Functor]
    (FToOut: F ~> λ[α => Option[X[α]]])
    (implicit N: Normalizable[X])
      : X[IT[F]] => Option[X[IT[F]]] = in => {
    coalesceTJ[F](FToOut).apply(in).flatMap(N.normalizeF(_: X[IT[F]]))
  }
}

trait CoalesceInstances {
  def coalesce[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT] = new CoalesceT[T]

  implicit def qscriptCore[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]
      : Coalesce.Aux[T, QScriptCore[T, ?]] =
    coalesce[T].qscriptCore

  implicit def projectBucket[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]
      : Coalesce.Aux[T, ProjectBucket[T, ?]] =
    coalesce[T].projectBucket

  implicit def thetaJoin[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]
      : Coalesce.Aux[T, ThetaJoin[T, ?]] =
    coalesce[T].thetaJoin

  implicit def equiJoin[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]
      : Coalesce.Aux[T, EquiJoin[T, ?]] =
    coalesce[T].equiJoin

  // TODO provide actual instance
  @SuppressWarnings(Array("org.wartremover.warts.Null"))
  implicit def coalesceCopK[T[_[_]], X <: TListK]: Coalesce.Aux[T, CopK[X, ?]] = null

  implicit def coproduct[T[_[_]], G[_], H[_]]
    (implicit G: Coalesce.Aux[T, G],
              H: Coalesce.Aux[T, H])
      : Coalesce.Aux[T, Coproduct[G, H, ?]] =
    new Coalesce[Coproduct[G, H, ?]] {
      type IT[F[_]] = T[F]

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, Coproduct[G, H, ?]]) =
        _.run.bitraverse(
          G.coalesceQC(PrismNT.inject[G, Coproduct[G, H, ?]] compose FToOut),
          H.coalesceQC(PrismNT.inject[H, Coproduct[G, H, ?]] compose FToOut)
        ) ∘ (Coproduct(_))

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, Coproduct[G, H, ?]]) =
        _.run.bitraverse(
          G.coalesceSR(PrismNT.inject[G, Coproduct[G, H, ?]] compose FToOut),
          H.coalesceSR(PrismNT.inject[H, Coproduct[G, H, ?]] compose FToOut)
        ) ∘ (Coproduct(_))

      def coalesceEJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[Coproduct[G, H, α]]]): Coproduct[G, H, IT[F]] => Option[Coproduct[G, H, IT[F]]] = {
        val i1: Coproduct[G, H, ?] ~> (Option ∘ G)#λ = PrismNT.inject[G, Coproduct[G, H, ?]].get
        val p1: F ~> (Option ∘ G)#λ = λ[F ~> (Option ∘ G)#λ](f => FToOut(f).flatMap(g => i1(g)))

        val i2: Coproduct[G, H, ?] ~> (Option ∘ H)#λ = PrismNT.inject[H, Coproduct[G, H, ?]].get
        val p2: F ~> (Option ∘ H)#λ = λ[F ~> (Option ∘ H)#λ](f => FToOut(f).flatMap(g => i2(g)))

        _.run.bitraverse(G.coalesceEJ(inj[F, G](FToOut)), H.coalesceEJ(inj[F, H](FToOut))) ∘ (Coproduct(_))
      }

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[Coproduct[G, H, α]]]) =
        _.run.bitraverse(G.coalesceTJ(inj[F, G](FToOut)), H.coalesceTJ(inj[F, H](FToOut))) ∘ (Coproduct(_))

      private def inj[F[_], Q[_]](
        FToOut: F ~> λ[α => Option[Coproduct[G, H, α]]]
      )(implicit I: Q :<: Coproduct[G, H, ?]): F ~> (Option ∘ Q)#λ = {
        λ[F ~> (Option ∘ Q)#λ](f => FToOut(f).flatMap(g => PrismNT.inject[Q, Coproduct[G, H, ?]].get(g)))
      }
    }

  def default[T[_[_]], X[_]]: Coalesce.Aux[T, X] =
    new Coalesce[X] {
      type IT[F[_]] = T[F]

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, X]) =
        κ(None)

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, X]) =
        κ(None)

      def coalesceEJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[X[α]]]) =
        κ(None)

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[X[α]]]) =
        κ(None)
    }

  implicit def deadEnd[T[_[_]]]: Coalesce.Aux[T, Const[DeadEnd, ?]] =
    default

  implicit def read[T[_[_]], A]: Coalesce.Aux[T, Const[Read[A], ?]] =
    default

  implicit def shiftedRead[T[_[_]], A]: Coalesce.Aux[T, Const[ShiftedRead[A], ?]] =
    default
}

class CoalesceT[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT] extends TTypes[T] {
  private def CoalesceTotal = Coalesce[T, QScriptTotal]

  private def freeTotal(branch: FreeQS)(
    coalesce: QScriptTotal[T[CoEnvQS]] => Option[QScriptTotal[T[CoEnvQS]]]):
      FreeQS = {
    val modify: T[CoEnvQS] => T[CoEnvQS] =
      _.cata((co: CoEnvQS[T[CoEnvQS]]) =>
        co.run.fold(
          κ(co),
          in => CoEnv[Hole, QScriptTotal, T[CoEnvQS]](
            repeatedly(coalesce)(in).right)).embed)

    applyCoEnvFrom[T, QScriptTotal, Hole](modify).apply(branch)
  }

  private def freeQC(branch: FreeQS): FreeQS =
    freeTotal(branch)(CoalesceTotal.coalesceQCNormalize(coenvPrism[QScriptTotal, Hole]))

  private def freeSR(branch: FreeQS): FreeQS = {
    def freeSR0[A](b: FreeQS)(implicit SR: Const[ShiftedRead[A], ?] :<<: QScriptTotal): FreeQS =
      freeTotal(b)(CoalesceTotal.coalesceSRNormalize[CoEnvQS, A](coenvPrism[QScriptTotal, Hole]))

    freeSR0[AFile](freeSR0[ADir](branch))
  }

  private def freeEJ(branch: FreeQS): FreeQS =
    freeTotal(branch)(CoalesceTotal.coalesceEJNormalize(coenvPrism[QScriptTotal, Hole].get))

  private def freeTJ(branch: FreeQS): FreeQS =
    freeTotal(branch)(CoalesceTotal.coalesceTJNormalize(coenvPrism[QScriptTotal, Hole].get))

  private def ifNeq(f: FreeQS => FreeQS): FreeQS => Option[FreeQS] =
    branch => {
      val coalesced = f(branch)
      (branch ≠ coalesced).option(coalesced)
    }

  private def makeBranched[A, B]
    (lOrig: A, rOrig: A)
    (op: A => Option[A])
    (f: (A, A) => B)
      : Option[B] =
    (op(lOrig), op(rOrig)) match {
      case (None, None) => None
      case (l,    r)    => f(l.getOrElse(lOrig), r.getOrElse(rOrig)).some
    }

  private def eliminateRightSideProj[A: Equal](func: FreeMapA[A], a: A): Option[FreeMapA[A]] = {
    val target = Free.point[MapFunc, A](a)
    val oneRef = Free.roll[MapFunc, A](MFC(ProjectIndex(target, IntLit(1))))
    val rightCount: Int = func.elgotPara[Int](count(target))

    // all `RightSide` access is through `oneRef`
    (func.elgotPara[Int](count(oneRef)) ≟ rightCount).option(
      func.transApoT(substitute(oneRef, target)))
  }

  private def eliminateRightSideProjUnary(fm: FreeMap): Option[FreeMap] =
    eliminateRightSideProj(fm, SrcHole)

  def qscriptCore: Coalesce.Aux[T, QScriptCore] =
    new Coalesce[QScriptCore] {
      type IT[F[_]] = T[F]

      def sequenceBucket[A: Equal, B](b: List[(A, B)]): Option[(Option[A], List[B])] =
        b.foldRightM[Option, (Option[A], List[B])](
          (None, Nil)) {
          case ((a, b), (as, bs)) =>
            as.fold[Option[Option[A]]](Some(a.some))(oldA => (oldA ≟ a).option(as)) strengthR (b :: bs)
        }

      // TODO: I feel like this must be some standard fold.
      def sequenceReduce[A: Equal, B](rf: ReduceFunc[(A, B)])
          : Option[(A, ReduceFunc[B])] =
        rf match {
          case ReduceFuncs.Count(a)           => (a._1, ReduceFuncs.Count(a._2)).some
          case ReduceFuncs.Sum(a)             => (a._1, ReduceFuncs.Sum(a._2)).some
          case ReduceFuncs.Min(a)             => (a._1, ReduceFuncs.Min(a._2)).some
          case ReduceFuncs.Max(a)             => (a._1, ReduceFuncs.Max(a._2)).some
          case ReduceFuncs.Avg(a)             => (a._1, ReduceFuncs.Avg(a._2)).some
          case ReduceFuncs.Arbitrary(a)       => (a._1, ReduceFuncs.Arbitrary(a._2)).some
          case ReduceFuncs.First(a)           => (a._1, ReduceFuncs.First(a._2)).some
          case ReduceFuncs.Last(a)            => (a._1, ReduceFuncs.Last(a._2)).some
          case ReduceFuncs.UnshiftArray(a)    => (a._1, ReduceFuncs.UnshiftArray(a._2)).some
          case ReduceFuncs.UnshiftMap(a1, a2) =>
            (a1._1 ≟ a2._1).option((a1._1, ReduceFuncs.UnshiftMap(a1._2, a2._2)))
        }

      def rightOnly(replacement: FreeMap): JoinFunc => Option[FreeMap] =
        _.traverseM[Option, Hole] {
          case LeftSide  => None
          case RightSide => replacement.some
        }

      val rewrite = new Rewrite[T]
      val nm = new NormalizableT[T]

      // TODO: Use this. It seems like a valid normalization, but it breaks
      //       autojoins. Maybe it can be applied as part of optimization, or as
      //       a connector-specific transformation.
      private def extractFilterFromQC[F[_]: Functor]
        (FToOut: QScriptCore ~> F)
          : QScriptCore[IT[F]] => Option[QScriptCore[IT[F]]] = {
        case LeftShift(src, struct, id, stpe, undef, repair) =>
          MapFuncCore.extractFilter(struct.linearize)(_.some) ∘ { case (f, m, _) =>
            LeftShift(FToOut(Filter(src, f.asRec)).embed, m.asRec, id, stpe, undef, repair)
          }
        case Map(src, mf) =>
          MapFuncCore.extractFilter(mf.linearize)(_.some) ∘ { case (f, m, _) =>
            Map(FToOut(Filter(src, f.asRec)).embed, m.asRec)
          }
        case _ => none
      }

      def fmIsCondUndef(jf: JoinFunc): Boolean = {
        val MapFuncCore = CopK.Inject[MapFuncCore, MapFunc]
        jf.resumeTwice.fold({
          case MapFuncCore(MapFuncsCore.Cond(_, _, -\/(MapFuncCore(MapFuncsCore.Undefined())))) => true
          case _ => false
        }, _ => false)
      }

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, QScriptCore]) = {
        case Map(Embed(src), mf) => FToOut.get(src) >>= (s =>
          if (mf.length ≟ 0 && (s match { case Unreferenced() => false; case _ => true }))
            Map(
              FToOut.reverseGet(Unreferenced[T, T[F]]()).embed,
              mf).some
          else s match {
            case Map(srcInner, mfInner) =>
              Map(srcInner, mf >> mfInner).some
            case LeftShift(srcInner, struct, id, stpe, undef, repair) =>
              LeftShift(srcInner, struct, id, stpe, undef, mf.linearize >> repair).some
            case Reduce(srcInner, bucket, funcs, repair) =>
              Reduce(srcInner, bucket, funcs, mf.linearize >> repair).some
            case Subset(innerSrc, lb, sel, rb) =>
              Subset(innerSrc,
                Free.roll(CopK.Inject[QScriptCore, QScriptTotal].inj(Map(lb, mf))),
                sel,
                rb).some
            case Filter(Embed(innerSrc), cond) => FToOut.get(innerSrc) >>= {
              case Map(doubleInner, mfInner) =>
                Map(
                  FToOut.reverseGet(Filter(
                    doubleInner,
                    cond >> mfInner)).embed,
                  mf >> mfInner).some
              case _ => None
            }
            case Sort(Embed(innerSrc), buckets, ordering) => FToOut.get(innerSrc) >>= {
              case Map(doubleInner, mfInner) =>
                Map(
                  FToOut.reverseGet(Sort(
                    doubleInner,
                    buckets ∘ (_ >> mfInner.linearize),
                    ordering ∘ (_.leftMap(_ >> mfInner.linearize)))).embed,
                  mf >> mfInner).some
              case _ => None
            }
/* FIXME: Investigate why this causes the 'convert union' test to fail.
            case Union(innerSrc, lBranch, rBranch) =>
              Union(
                innerSrc,
                Free.roll(Inject[QScriptCore, QScriptTotal].inj(Map(lBranch, mf))),
                Free.roll(Inject[QScriptCore, QScriptTotal].inj(Map(rBranch, mf)))).some
*/
            case _ => None
          })
        case LeftShift(Embed(src), struct, id, stpe, undef, shiftRepair) =>
          FToOut.get(src) >>= {
            case LeftShift(innerSrc, innerStruct, innerId, innerStpe, innerUndef, innerRepair)
                if !shiftRepair.element(LeftSide) && !fmIsCondUndef(shiftRepair) && struct ≠ HoleR =>
              LeftShift(
                FToOut.reverseGet(LeftShift(
                  innerSrc,
                  innerStruct,
                  innerId,
                  innerStpe,
                  innerUndef,
                  struct.linearize >> innerRepair)).embed,
                HoleR,
                id,
                stpe,
                OnUndefined.omit,
                shiftRepair).some
            // TODO: Should be able to apply this where there _is_ a `LeftSide`
            //       reference, but currently that breaks merging.
            case Map(innerSrc, mf) if !shiftRepair.element(LeftSide) =>
              LeftShift(innerSrc, struct >> mf, id, stpe, OnUndefined.omit, shiftRepair).some
            case Reduce(srcInner, _, List(ReduceFuncs.UnshiftArray(elem)), redRepair)
                if nm.freeMF(struct.linearize >> redRepair) ≟ Free.point(ReduceIndex(0.right)) =>
              rightOnly(elem)(shiftRepair) ∘ (RecFreeS.fromFree(_)) ∘ (Map(srcInner, _))
            case Reduce(srcInner, _, List(ReduceFuncs.UnshiftMap(k, elem)), redRepair)
                if nm.freeMF(struct.linearize >> redRepair) ≟ Free.point(ReduceIndex(0.right)) =>
              rightOnly(id match {
                case ExcludeId => elem
                case IdOnly    => k
                case IncludeId => StaticArray(List(k, elem))
              })(shiftRepair) ∘ (RecFreeS.fromFree(_)) ∘ (Map(srcInner, _))
            case _ => None
          }
        case Reduce(Embed(src), bucket, reducers, redRepair) =>
          FToOut.get(src) >>= {
            case LeftShift(innerSrc, struct, id, stpe, _, shiftRepair)
                if shiftRepair =/= RightSideF =>
              (bucket.traverse(b => rightOnly(HoleF)(nm.freeMF(b >> shiftRepair))) ⊛
                reducers.traverse(_.traverse(mf => rightOnly(HoleF)(nm.freeMF(mf >> shiftRepair)))))((sb, sr) =>
                Reduce(
                  FToOut.reverseGet(LeftShift(innerSrc, struct, id, stpe, OnUndefined.omit, RightSideF)).embed,
                  sb,
                  sr,
                  redRepair))
            case LeftShift(innerSrc, struct, id, stpe, _, shiftRepair) =>
              (bucket.traverse(b => rewrite.rewriteShift(id, nm.freeMF(b >> shiftRepair))).flatMap(sequenceBucket[IdStatus, JoinFunc]) ⊛
                reducers.traverse(_.traverse(mf =>
                  rewrite.rewriteShift(id, nm.freeMF(mf >> shiftRepair)))).flatMap(_.traverse(sequenceReduce[IdStatus, JoinFunc]) >>= sequenceBucket[IdStatus, ReduceFunc[JoinFunc]])) {
                case ((bId, bucket), (rId, reducers)) =>
                  val newId = bId.fold(rId.getOrElse(ExcludeId).some)(b => rId.fold(b.some)(r => (b ≟ r).option(b)))
                  newId strengthR ((bucket, reducers))
              }.join >>= {
                case (newId, (bucket, reducers)) =>
                  (bucket.traverse(rightOnly(HoleF)) ⊛
                    (reducers.traverse(_.traverse(rightOnly(HoleF)))))((sb, sr) =>
                    Reduce(
                      FToOut.reverseGet(LeftShift(innerSrc, struct, newId, stpe, OnUndefined.omit, RightSideF)).embed,
                      sb,
                      sr,
                      redRepair))
              }
            case Map(innerSrc, mf) =>
              Reduce(
                innerSrc,
                bucket ∘ (_ >> mf.linearize),
                reducers.map(_.map(_ >> mf.linearize)),
                redRepair).some
            case Sort(innerSrc, _, _)
                if !reducers.exists(ReduceFunc.isOrderDependent) =>
              Reduce(innerSrc, bucket, reducers, redRepair).some
            case _ => None
          }
        case Filter(Embed(src), cond) => FToOut.get(src) >>= {
          case Filter(srcInner, condInner) =>
            Filter(srcInner, RecFreeS.roll[MapFunc, Hole](MFC(And(condInner, cond)))).some
          case _ => None
        }
        case Subset(src, from, sel, count) =>
          makeBranched(from, count)(ifNeq(freeQC))(Subset(src, _, sel, _))
        case Union(src, from, count) =>
          makeBranched(from, count)(ifNeq(freeQC))(Union(src, _, _))
        case _ => None
      }

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, QScriptCore]) = {
        case Subset(src, from, sel, count) =>
          makeBranched(from, count)(ifNeq(freeSR))(Subset(src, _, sel, _))
        case Union(src, from, count) =>
          makeBranched(from, count)(ifNeq(freeSR))(Union(src, _, _))
        case _ => None
      }

      def coalesceEJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[QScriptCore[α]]]) = {
        case Subset(src, from, sel, count) =>
          makeBranched(from, count)(ifNeq(freeEJ))((l, r) => Subset(src, l, sel, r))
        case Union(src, from, count) =>
          makeBranched(from, count)(ifNeq(freeEJ))((l, r) => Union(src, l, r))
        case _ => None
      }

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[QScriptCore[α]]]) = {
        case Subset(src, from, sel, count) =>
          makeBranched(from, count)(ifNeq(freeTJ))((l, r) => Subset(src, l, sel, r))
        case Union(src, from, count) =>
          makeBranched(from, count)(ifNeq(freeTJ))((l, r) => Union(src, l, r))
        case _ => None
      }
    }

  def projectBucket: Coalesce.Aux[T, ProjectBucket] =
    new Coalesce[ProjectBucket] {
      type IT[F[_]] = T[F]

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, ProjectBucket]) = {
        κ(None)
      }

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, ProjectBucket]) =
        κ(None)

      def coalesceEJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[ProjectBucket[α]]]) =
        κ(None)

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[ProjectBucket[α]]]) =
        κ(None)
    }

  def thetaJoin: Coalesce.Aux[T, ThetaJoin] =
    new Coalesce[ThetaJoin] {
      type IT[F[_]] = T[F]

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, ThetaJoin]) =
        tj => makeBranched(
          tj.lBranch, tj.rBranch)(
          ifNeq(freeQC))(
          ThetaJoin(tj.src, _, _, tj.on, tj.f, tj.combine))

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, ThetaJoin]) =
        tj => makeBranched(
          tj.lBranch, tj.rBranch)(
          ifNeq(freeSR))(
          ThetaJoin(tj.src, _, _, tj.on, tj.f, tj.combine))

      def coalesceEJ[F[_]: Functor]
      (FToOut: F ~> λ[α => Option[ThetaJoin[α]]]) =
        tj => makeBranched(
          tj.lBranch, tj.rBranch)(
          ifNeq(freeEJ))((l, r) =>
          ThetaJoin(tj.src, l, r, tj.on, tj.f, tj.combine))

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[ThetaJoin[α]]]) =
        tj => makeBranched(
          tj.lBranch, tj.rBranch)(
          ifNeq(freeTJ))((l, r) =>
          ThetaJoin(tj.src, l, r, tj.on, tj.f, tj.combine))
    }

  def equiJoin: Coalesce.Aux[T, EquiJoin] =
    new Coalesce[EquiJoin] {
      type IT[F[_]] = T[F]

      def coalesceQC[F[_]: Functor]
        (FToOut: PrismNT[F, EquiJoin]) =
        (ej: EquiJoin[IT[F]]) => {
          val branched: Option[EquiJoin[T[F]]] = makeBranched(
            ej.lBranch, ej.rBranch)(
            ifNeq(freeQC))(
            EquiJoin(ej.src, _, _, ej.key, ej.f, ej.combine))

          val qct = CopK.Inject[QScriptCore, QScriptTotal]

          def coalesceBranchMaps(ej: EquiJoin[T[F]]): Option[EquiJoin[T[F]]] = {
            def coalesceSide(branch: FreeQS, key: List[FreeMap], side: JoinSide):
                Option[(FreeQS, List[FreeMap], JoinFunc)] =
              branch.project.run.map(qct.prj.apply) match {
                case \/-(Some(Map(innerSrc, mf))) => (innerSrc, key ∘ (_ >> mf.linearize), mf.linearize.as(side)).some
                case _ => none
              }

            (coalesceSide(ej.lBranch, ej.key ∘ (_._1), LeftSide) |@| coalesceSide(ej.rBranch, ej.key ∘ (_._2), RightSide)) {
              case ((lSrc, lKey, lComb), (rSrc, rKey, rComb)) =>
                val combine = ej.combine >>= {
                  case LeftSide => lComb
                  case RightSide => rComb
                }
                EquiJoin(ej.src, lSrc, rSrc, lKey zip rKey, ej.f, combine)
            }
          }
          coalesceBranchMaps(branched.getOrElse(ej)) orElse branched
        }

      def coalesceSR[F[_]: Functor, A]
        (FToOut: PrismNT[F, EquiJoin]) =
        ej => makeBranched(
          ej.lBranch, ej.rBranch)(
          ifNeq(freeSR))(
          EquiJoin(ej.src, _, _, ej.key, ej.f, ej.combine))

      def coalesceEJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[EquiJoin[α]]]) =
        ej => makeBranched(
          ej.lBranch, ej.rBranch)(
          ifNeq(freeEJ))((l, r) =>
          EquiJoin(ej.src, l, r, ej.key, ej.f, ej.combine))

      def coalesceTJ[F[_]: Functor]
        (FToOut: F ~> λ[α => Option[EquiJoin[α]]]) =
        ej => makeBranched(
          ej.lBranch, ej.rBranch)(
          ifNeq(freeTJ))((l, r) =>
          EquiJoin(ej.src, l, r, ej.key, ej.f, ej.combine))
    }
}

object Coalesce extends CoalesceInstances {
  type Aux[T[_[_]], X[_]] = Coalesce[X] {
    type IT[F[_]] = T[F]
  }

  def apply[T[_[_]], X[_]](implicit ev: Coalesce.Aux[T, X]) = ev
}
