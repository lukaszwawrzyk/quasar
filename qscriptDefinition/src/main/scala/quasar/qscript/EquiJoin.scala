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

package quasar.qscript

import slamdata.Predef._
import quasar.{NonTerminal, RenderTree, RenderTreeT}, RenderTree.ops._
import quasar.common.JoinType
import quasar.contrib.matryoshka._
import quasar.fp._

import matryoshka._
import matryoshka.data._
import monocle.macros.Lenses
import scalaz._, Scalaz._

/** This is an optional component of QScript that can be used instead of
  * ThetaJoin. It’s easier to implement, but more restricted (where ThetaJoin
  * has an arbitrary predicate to determine if a pair of records should be
  * combined, EquiJoin has an expression on each side that is compared with
  * simple equality).
  */
@Lenses final case class EquiJoin[T[_[_]], A](
  src: A,
  lBranch: FreeQS[T],
  rBranch: FreeQS[T],
  key: List[(FreeMap[T], FreeMap[T])],
  f: JoinType,
  // TODO: This could potentially also index into the key.
  combine: JoinFunc[T])

object EquiJoin {
  /*
  Missing Equal for FreeQS[T] which for Coproducts resolves to:

  scalaz.Equal.apply[quasar.qscript.FreeQS[T]](matryoshka.`package`.delayEqual[[A]scalaz.Free[[$72$]scalaz.Coproduct[[$0$]quasar.qscript.QScriptCore[T,$0$],[$1$]scalaz.Coproduct[[$2$]quasar.qscript.ProjectBucket[T,
$2$],[$3$]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.A
bs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]sca
laz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxe
d]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5$],$3$],$1$],$72$],A], quasar.qscript.Hole](qscript.this.Hole.equal, matryoshka.data.`package`.freeEqual[[A]scalaz.Coproduct[
[$0$]quasar.qscript.QScriptCore[T,$0$],[$1$]scalaz.Coproduct[[$2$]quasar.qscript.ProjectBucket[T,$2$],[$3$]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[$6$]quasar.qscript.EquiJo
in[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pat
hy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coprod
uct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5$],$3$],$1$],A]](scal
az.this.Coproduct.coproductTraverse[[A]quasar.qscript.QScriptCore[T,A], [A]scalaz.Coproduct[[$2$]quasar.qscript.ProjectBucket[T,$2$],[$3$]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[
$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasa
r.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$1
2$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5
$],$3$],A]](qscript.this.QScriptCore.traverse[T], scalaz.this.Coproduct.coproductTraverse[[A]quasar.qscript.ProjectBucket[T,A], [A]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[$6$]quasar.
qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.S
hiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$
]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5$],A]](qscr
ipt.this.ProjectBucket.traverse[T], scalaz.this.Coproduct.coproductTraverse[[A]quasar.qscript.ThetaJoin[T,A], [A]scalaz.Coproduct[[$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.
ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[
$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,
pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],A]](qscript.this.ThetaJoin.traverse[T], scalaz.this.Coproduct.coproductTraverse[[A]quasar.qscript.Eq
uiJoin[T,A], [A]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.
Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct
[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],A]](EquiJoin.this.traverse[T], scalaz.t
his.Coproduct.coproductTraverse[[B]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],B], [A]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.P
ath.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]sca
laz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],A]](scalaz.this.Const.constTraverse[quasar.qscript.Shifted
Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]]], scalaz.this.Coproduct.coproductTraverse[[B]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],B], [A]sca
laz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path
.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],A]](scalaz.this.Const.constTraverse[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]]], sc
alaz.this.Coproduct.coproductTraverse[[B]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],B], [A]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,
pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],A]](scalaz.this.Const.constTraverse[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]]], scalaz.t
his.Coproduct.coproductTraverse[[B]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],B], [B]scalaz.Const[quasar.qscript.DeadEnd,B]](scalaz.this.Const.constTraverse[quasar.qscript.Re
ad[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]]], scalaz.this.Const.constTraverse[quasar.qscript.DeadEnd])))))))), quasar.fp.`package`.coproductEqual[[A]quasar.qscript.QScriptCore[T,A], [A]scalaz.Coproduct[[
$2$]quasar.qscript.ProjectBucket[T,$2$],[$3$]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript
.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],
[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs
,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5$],$3$],A]](qscript.this.QScriptCore.equal[T](evidence$1, evidence$2), quasar.fp.`package`.co
productEqual[[A]quasar.qscript.ProjectBucket[T,A], [A]scalaz.Coproduct[[$4$]quasar.qscript.ThetaJoin[T,$4$],[$5$]scalaz.Coproduct[[$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qs
cript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$
10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Pat
h.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],$5$],A]](qscript.this.ProjectBucket.equal[T](evidence$1, evidence$2), quasar.fp.`package`.co
productEqual[[A]quasar.qscript.ThetaJoin[T,A], [A]scalaz.Coproduct[[$6$]quasar.qscript.EquiJoin[T,$6$],[$7$]scalaz.Coproduct[[$8$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path
.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Rea
d[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.C
onst[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],$7$],A]](qscript.this.ThetaJoin.equal[T](evidence$1, evidence$2), quasar.fp.`package`.coproductEqual[[A]quasar.qscript.EquiJoin[T,A], [A]scalaz.Coproduct[[$8$]scalaz.
Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$8$],[$9$]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.
Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy
.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],$9$],A]](EquiJoin.this.equal[T](evidence$1, evidence$2), quasar.fp.`package`.coproductEqual
[[B]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],B], [A]scalaz.Coproduct[[$10$]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.P
ath.Sandboxed]],$10$],[$11$]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[p
athy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],$13$],$11$],A]](quasar.fp.`package`.constEqual[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,p
athy.Path.Dir,pathy.Path.Sandboxed]]](qscript.this.ShiftedRead.equal[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]](pathy.this.Path.pathOrder[pathy.Path.Abs, pathy.Path.Dir, pathy.Path.Sandboxed])), quasar.fp.`pa
ckage`.coproductEqual[[B]scalaz.Const[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],B], [A]scalaz.Coproduct[[$12$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Pa
th.Dir,pathy.Path.Sandboxed]],$12$],[$13$]scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],
$13$],A]](quasar.fp.`package`.constEqual[quasar.qscript.ShiftedRead[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]]](qscript.this.ShiftedRead.equal[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed
]](pathy.this.Path.pathOrder[pathy.Path.Abs, pathy.Path.File, pathy.Path.Sandboxed])), quasar.fp.`package`.coproductEqual[[B]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]],B], [A]
scalaz.Coproduct[[$14$]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],$14$],[$15$]scalaz.Const[quasar.qscript.DeadEnd,$15$],A]](quasar.fp.`package`.constEqual[quasar.qscr
ipt.Read[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]]](qscript.this.Read.equal[pathy.Path[pathy.Path.Abs,pathy.Path.Dir,pathy.Path.Sandboxed]](pathy.this.Path.pathOrder[pathy.Path.Abs, pathy.Path.Dir, pathy.Pat
h.Sandboxed])), quasar.fp.`package`.coproductEqual[[B]scalaz.Const[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]],B], [B]scalaz.Const[quasar.qscript.DeadEnd,B]](quasar.fp.`package`.constEqual
[quasar.qscript.Read[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]]](qscript.this.Read.equal[pathy.Path[pathy.Path.Abs,pathy.Path.File,pathy.Path.Sandboxed]](pathy.this.Path.pathOrder[pathy.Path.Abs, pathy.Path.
File, pathy.Path.Sandboxed])), quasar.fp.`package`.constEqual[quasar.qscript.DeadEnd](qscript.this.DeadEnd.equal))))))))))))


        scalaz.Equal.apply(
          matryoshka.delayEqual(
            Hole.equal,
            matryoshka.data.freeEqual(
              Coproduct.coproductTraverse(
                QScriptCore.traverse,
                Coproduct.coproductTraverse(
                  ProjectBucket.traverse,
                  Coproduct.coproductTraverse(
                    ThetaJoin.traverse,
                    Coproduct.coproductTraverse(
                      EquiJoin.traverse,
                      Coproduct.coproductTraverse(
                        Const.constTraverse,
                        Coproduct.coproductTraverse(
                          Const.constTraverse,
                          Coproduct.coproductTraverse(
                            Const.constTraverse,
                            Coproduct.coproductTraverse(
                              Const.constTraverse,
                              Const.constTraverse)))))))),
              quasar.fp.coproductEqual(
                QScriptCore.equal(evidence$1, evidence$2),
                quasar.fp.coproductEqual(
                  ProjectBucket.equal(evidence$1, evidence$2),
                  quasar.fp.coproductEqual(
                    ThetaJoin.equal(evidence$1, evidence$2),
                    quasar.fp.coproductEqual(
                      EquiJoin.equal(evidence$1, evidence$2),
                      quasar.fp.coproductEqual(
                        quasar.fp.constEqual(ShiftedRead.equal(pathy.Path.pathOrder)),
                        quasar.fp.coproductEqual(
                          quasar.fp.constEqual(ShiftedRead.equal(pathy.Path.pathOrder)),
                          quasar.fp.coproductEqual(
                            quasar.fp.constEqual(Read.equal(pathy.Path.pathOrder)),
                            quasar.fp.coproductEqual(
                              quasar.fp.constEqual(Read.equal(pathy.Path.pathOrder)),
                              quasar.fp.constEqual(DeadEnd.equal))))))))))))

  * */

  implicit def equal[T[_[_]]: BirecursiveT: EqualT]:
      Delay[Equal, EquiJoin[T, ?]] =
    new Delay[Equal, EquiJoin[T, ?]] {
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (EquiJoin(a1, l1, r1, k1, f1, c1),
                EquiJoin(a2, l2, r2, k2, f2, c2)) =>
            eq.equal(a1, a2) &&
            l1 ≟ l2 &&
            r1 ≟ r2 &&
            k1 ≟ k2 &&
            f1 ≟ f2 &&
            c1 ≟ c2
        }
    }

  implicit def show[T[_[_]]: ShowT]: Delay[Show, EquiJoin[T, ?]] =
    new Delay[Show, EquiJoin[T, ?]] {
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def apply[A](showA: Show[A]): Show[EquiJoin[T, A]] = Show.show {
        case EquiJoin(src, lBr, rBr, key, f, combine) =>
          Cord("EquiJoin(") ++
          showA.show(src) ++ Cord(",") ++
          lBr.show ++ Cord(",") ++
          rBr.show ++ Cord(",") ++
          key.show ++ Cord(",") ++
          f.show ++ Cord(",") ++
          combine.show ++ Cord(")")
      }
    }

  implicit def renderTree[T[_[_]]: RenderTreeT: ShowT]: Delay[RenderTree, EquiJoin[T, ?]] =
    new Delay[RenderTree, EquiJoin[T, ?]] {
      val nt = List("EquiJoin")
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def apply[A](r: RenderTree[A]): RenderTree[EquiJoin[T, A]] = RenderTree.make {
          case EquiJoin(src, lBr, rBr, key, tpe, combine) =>
            NonTerminal(nt, None, List(
              r.render(src),
              lBr.render,
              rBr.render,
              key.render,
              tpe.render,
              combine.render))
        }
      }

  implicit def traverse[T[_[_]]]: Traverse[EquiJoin[T, ?]] =
    new Traverse[EquiJoin[T, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: EquiJoin[T, A])(
        f: A => G[B]) =
        f(fa.src) ∘
          (EquiJoin(_, fa.lBranch, fa.rBranch, fa.key, fa.f, fa.combine))
    }
}
