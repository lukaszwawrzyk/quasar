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

package quasar.physical.mongodb

import slamdata.Predef._
import quasar.{RenderTree, Terminal}
import quasar.fp.{:<<:, ACopK, copkTraverse}

import matryoshka._
import matryoshka.data.Fix
import matryoshka.implicits._
import monocle.Prism
import scalaz._, Scalaz._
import iotaz.{CopK, TNilK}
import iotaz.TListK.:::

package object expression {

  /** The type for expressions targeting MongoDB 3.2 specifically. */
  type Expr3_2[A] = ExprOpCoreF[A]
  /** The type for expressions targeting MongoDB 3.4 specifically. */
  type Expr3_4L = ExprOp3_4F ::: ExprOpCoreF ::: TNilK
  type Expr3_4[A] = CopK[Expr3_4L, A]
  /** The type for expressions targeting MongoDB 3.4.4 specifically. */
  type Expr3_4_4L = ExprOp3_4_4F ::: Expr3_4L
  type Expr3_4_4[A] = CopK[Expr3_4_4L, A]
  /** The type for expressions targeting MongoDB 3.6 specifically. */
  type Expr3_6L = ExprOp3_6F ::: Expr3_4_4L
  type Expr3_6[A] = CopK[Expr3_6L, A]

  /** The type for expressions supporting the most advanced capabilities. */
  type ExprOp[A] = Expr3_6[A]

  val fixExprOp =
    new ExprOpCoreF.fixpoint[Fix[ExprOp], ExprOp](_.embed)

  def fixExprOpCore[EX[a] <: ACopK[a]: Functor]
    (implicit I: ExprOpCoreF :<<: EX) =
    new ExprOpCoreF.fixpoint[Fix[EX], EX](_.embed)

  val DocField = Prism.partial[DocVar, BsonField] {
    case DocVar.ROOT(Some(tail)) => tail
  } (DocVar.ROOT(_))

  // FIXME: no way to put this in anybody's companion where it will be found?
  implicit def exprOpRenderTree[T[_[_]]: RecursiveT, EX[_]: Functor](implicit ops: ExprOpOps.Uni[EX]): RenderTree[T[EX]] =
    new RenderTree[T[EX]] {
      def render(v: T[EX]) = Terminal(List("ExprOp"), v.cata(ops.bson).toJs.pprint(0).some)
    }
}
