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

// TODO adjust package, or find a better place for this. For now it will stay here, to be decided later
package quasar.qscript

import slamdata.Predef._
import scalaz._, Scalaz._
import quasar.fp.ACopK
import iotaz.CopK

/** This is like [[scalaz.Inject]], but for injecting an arbitrary coproduct
  * where all of the components are in the `OUT` coproduct in any order.
  *
  * It _may_ be unprincipled (otherwise, why not allow [[scalaz.Inject]] to work
  * this way directly?) But it is temporarily necessary in order to “inject” our
  * more constrained versions of QScript into [[QScriptTotal]].
  */
trait Injectable[IN[_]] {
  type OUT[A]
  def inj: IN ~> OUT
  def prj: OUT ~> λ[A => Option[IN[A]]]
  final def apply[A](fa: IN[A]): OUT[A] = inj(fa)
  final def unapply[A](ga: OUT[A]): Option[IN[A]] = prj(ga)
}

object Injectable extends InjectableInstances {

  def id[F[_]]: Aux[F, F] = make(
    NaturalTransformation.refl[F],
    λ[F ~> λ[A => Option[F[A]]]](Some(_))
  )

}

sealed trait InjectableInstances extends InjectableInstances0 {

  /** Note: you'd like this to be implicit, but that makes implicit search
    * quadratic, so instead this is provided so that you can manually construct
    * instances where they're needed. */
  def coproduct[F[_], G[_], H[_]](implicit F: Aux[F, H], G: Aux[G, H]): Aux[Coproduct[F, G, ?], H] = make(
    λ[Coproduct[F, G, ?] ~> H](_.run.fold(F.inj, G.inj)),
    λ[H ~> λ[A => Option[Coproduct[F, G, A]]]](out =>
      F.prj(out).cata(
        f => Coproduct(f.left).some,
        G.prj(out) ∘ (g => Coproduct(g.right))
      )
    )
  )

  implicit def injectCopK[F[_], G[_] <: ACopK](implicit IN: CopK.Inject[F, G]): Aux[F, G] =
    make[F, G](IN.inj, IN.prj)

  implicit def reflexiveInjectInstance[F[_]]: Injectable.Aux[F, F] =
    make[F, F](λ[F ~> F](x => x), λ[F ~> λ[A => Option[F[A]]]](some(_)))

}

sealed trait InjectableInstances0 extends InjectableBase {

  implicit def inject[F[_], G[_]](implicit IN: F :<: G): Aux[F, G] =
    make[F, G](IN, λ[G ~> λ[A => Option[F[A]]]](IN prj _))

}

sealed trait InjectableBase {

  type Aux[IN[_], F[_]] = Injectable[IN] { type OUT[A] = F[A] }

  def make[F[_], G[_]](inject: F ~> G, project: G ~> λ[A => Option[F[A]]]): Aux[F, G] = new Injectable[F] {
    type OUT[A] = G[A]
    val inj  = inject
    val prj = project
  }

}