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

import quasar.contrib.pathy._
import quasar.fp._
import quasar.fs._
import quasar.qscript._

import matryoshka._
import matryoshka.implicits._
import scalaz._
import scalaz.syntax.all._
import iotaz.CopK
import iotaz.TNilK
import slamdata.Predef.Int

sealed trait Unirewrite[T[_[_]], C[_] <: ACopK] {
  def apply[F[_]: Monad: MonadFsErr](r: Rewrite[T], lc: DiscoverPath.ListContents[F]): T[QScriptRead[T, ?]] => F[T[C]]
}

private[qscript] trait UnirewriteLowPriorityImplicits {
  // TODO make it real
  private type C0[C[x] <: CopK[_, x], A] = CopK[TNilK, A]

  implicit def fileRead[T[_[_]]: BirecursiveT, C[_] <: ACopK](
    implicit
      FC: Functor[C],
      TC0: Traverse[C0[C, ?]],
      J: SimplifyJoin.Aux[T, QScriptShiftRead[T, ?], C0[C, ?]],
      C: Coalesce.Aux[T, QScriptShiftRead[T, ?], QScriptShiftRead[T, ?]],
      N: Normalizable[QScriptShiftRead[T, ?]],
      E: ExpandDirs.Aux[T, C0[C, ?], C]): Unirewrite[T, C] = new Unirewrite[T, C] {

    def apply[F[_]: Monad: MonadFsErr](r: Rewrite[T], lc: DiscoverPath.ListContents[F]): T[QScriptRead[T, ?]] => F[T[C]] = { qs =>
      r.simplifyJoinOnShiftRead[QScriptRead[T, ?], QScriptShiftRead[T, ?], C0[C, ?]]
        .apply(qs)
        .transCataM(E.expandDirs(reflNT[C], lc))
    }
  }
}

object Unirewrite extends UnirewriteLowPriorityImplicits {

  implicit def dirRead[T[_[_]], C[_] <: ACopK](
    implicit
      D: Const[ShiftedRead[ADir], ?] :<<: C,
      T: Traverse[C],
      QC: QScriptCore[T, ?] :<<: C,
      TJ: ThetaJoin[T, ?] :<<: C,
      GI: Injectable.Aux[C, QScriptTotal[T, ?]],
      S: ShiftReadDir.Aux[T, QScriptRead[T, ?], C],
      C: Coalesce.Aux[T, C, C],
      N: Normalizable[C]): Unirewrite[T, C] = new Unirewrite[T, C] {

    def apply[F[_]: Monad: MonadFsErr](r: Rewrite[T], lc: DiscoverPath.ListContents[F]): T[QScriptRead[T, ?]] => F[T[C]] =
      r.shiftReadDir[QScriptRead[T, ?], C] andThen (_.point[F])
  }

  def apply[T[_[_]], C[_] <: ACopK, F[_]: Monad: MonadFsErr](r: Rewrite[T], lc: DiscoverPath.ListContents[F])(implicit U: Unirewrite[T, C]) =
    U(r, lc)
}
