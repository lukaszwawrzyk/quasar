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

package quasar.qsu

import slamdata.Predef._
import quasar.RenderTreeT
import quasar.fs.Planner.{ PlannerError, PlannerErrorME }
import quasar.effect.NameGenerator
import quasar.frontend.logicalplan.LogicalPlan
import matryoshka.{ BirecursiveT, EqualT, ShowT }
import scalaz.{ EitherT, Functor, Monad, StateT, Kleisli => K }

final class LPtoQS[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT] extends QSUTTypes[T] {
  import LPtoQS.MapSyntax

  def apply[M[_]: Monad](lp: T[LogicalPlan])(implicit
    Ku: PlannerErrorME[EitherT[StateT[M, Long, ?], PlannerError, ?]],
    R: NameGenerator[EitherT[StateT[M, Long, ?], PlannerError, ?]],
    W: Monad[EitherT[StateT[M, Long, ?], PlannerError, ?]],
    SSS: scalaz.Show[T[LogicalPlan]],
    ZZZ: scalaz.Show[quasar.frontend.logicalplan.LogicalPlan[quasar.qsu.QSUGraph[T]]]
  )
  : EitherT[StateT[M, Long, ?], PlannerError, T[QScriptEducated]] = {
    type F[x] = EitherT[StateT[M, Long, ?], PlannerError, x]

    val agraph =
      ApplyProvenance.AuthenticatedQSU.graph[T]

    val lpToQs =
      K(ReadLP[T, M])                        >==>
        RewriteGroupByArrays[T, F]             >-
        EliminateUnary[T]                      >-
        RecognizeDistinct[T]                   >==>
        ExtractFreeMap[T, F]                   >==>
        ApplyProvenance[T, F]                  >==>
        ReifyBuckets[T, F]                     >==>
        MinimizeAutoJoins[T, F]                >==>
        ReifyAutoJoins[T, F]                   >==>
        ExpandShifts[T, F]                     >-
        agraph.modify(ResolveOwnIdentities[T]) >==>
        ReifyIdentities[T, F]                  >==>
        Graduate[T, F]

    lpToQs(lp)
  }

}

object LPtoQS {
  def apply[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]: LPtoQS[T] = new LPtoQS[T]

  final implicit class MapSyntax[F[_], A](val self: F[A]) extends AnyVal {
    def >-[B](f: A => B)(implicit F: Functor[F]): F[B] =
      F.map(self)(f)
  }
}
