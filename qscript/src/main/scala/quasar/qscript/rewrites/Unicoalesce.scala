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

import slamdata.Predef._
import quasar.contrib.matryoshka._
import quasar.fp._
import quasar.fp.ski._
import quasar.qscript._

import matryoshka._
import scalaz._

sealed trait Unicoalesce[T[_[_]], C[_] <: ACopK] {
  def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]): C[T[C]] => Option[C[T[C]]]
}

object Unicoalesce {

  /**
   * Provides a convenient way of capturing all of the Unicoalesce
   * dependencies in a single implicit, which can then be passed
   * along as a value (e.g. in BackendModule).
   */
  trait Capture[T[_[_]], C[_] <: ACopK] {
    val C: Coalesce.Aux[T, C, C]
    val F: Functor[C]
    val QC: UnicoalesceQC[T, C]
    val SR: UnicoalesceSR[T, C]
    val EJ: UnicoalesceEJ[T, C]
    val TJ: UnicoalesceTJ[T, C]
    val N: Normalizable[C]

    def run: C[T[C]] => C[T[C]] =
      apply[T, C](C, F, QC, SR, EJ, TJ, N)
  }

  object Capture {

    implicit def materialize[T[_[_]], C[_] <: ACopK](
      implicit
        _C: Coalesce.Aux[T, C, C],
        _F: Functor[C],
        _QC: UnicoalesceQC[T, C],
        _SR: UnicoalesceSR[T, C],
        _EJ: UnicoalesceEJ[T, C],
        _TJ: UnicoalesceTJ[T, C],
        _N: Normalizable[C]): Capture[T, C] = new Capture[T, C] {

      val C = _C
      val F = _F
      val QC = _QC
      val SR = _SR
      val EJ = _EJ
      val TJ = _TJ
      val N = _N
    }

    def apply[T[_[_]], C[_] <: ACopK](implicit C: Capture[T, C]) = C
  }

  def apply[T[_[_]], C[_] <: ACopK](
    implicit
      C: Coalesce.Aux[T, C, C],
      F: Functor[C],
      QC: UnicoalesceQC[T, C],
      SR: UnicoalesceSR[T, C],
      EJ: UnicoalesceEJ[T, C],
      TJ: UnicoalesceTJ[T, C],
      N: Normalizable[C]): C[T[C]] => C[T[C]] =
    repeatedly(
      applyTransforms(
        QC(C),
        SR(C),
        EJ(C),
        TJ(C),
        N.normalizeF(_: C[T[C]])))
}

sealed trait UnicoalesceQC[T[_[_]], C[_] <: ACopK] extends Unicoalesce[T, C]

private[qscript] trait UnicoalesceQCLowPriorityImplicits {
  implicit def default[T[_[_]], C[_] <: ACopK]: UnicoalesceQC[T, C] = new UnicoalesceQC[T, C] {
    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) = κ(None)
  }
}

object UnicoalesceQC extends UnicoalesceQCLowPriorityImplicits {

  implicit def member[T[_[_]], C[_] <: ACopK](
    implicit
      QC: QScriptCore[T, ?] :<<: C): UnicoalesceQC[T, C] = new UnicoalesceQC[T, C] {

    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) =
      C.coalesceQC[C](idPrism)
  }
}

sealed trait UnicoalesceSR[T[_[_]], C[_] <: ACopK] extends Unicoalesce[T, C]

private[qscript] trait UnicoalesceSRLowPriorityImplicits {
  implicit def default[T[_[_]], C[_] <: ACopK]: UnicoalesceSR[T, C] = new UnicoalesceSR[T, C] {
    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) = κ(None)
  }
}

object UnicoalesceSR extends UnicoalesceSRLowPriorityImplicits {

  // TODO the A might not infer here
  implicit def member[T[_[_]], A, C[_] <: ACopK](
    implicit
      QC: QScriptCore[T, ?] :<<: C,
      SR: Const[ShiftedRead[A], ?] :<<: C): UnicoalesceSR[T, C] = new UnicoalesceSR[T, C] {

    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) =
      C.coalesceSR[C, A](idPrism)
  }
}

sealed trait UnicoalesceEJ[T[_[_]], C[_] <: ACopK] extends Unicoalesce[T, C]

private[qscript] trait UnicoalesceEJLowPriorityImplicits {
  implicit def default[T[_[_]], C[_] <: ACopK]: UnicoalesceEJ[T, C] = new UnicoalesceEJ[T, C] {
    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) = κ(None)
  }
}

object UnicoalesceEJ extends UnicoalesceEJLowPriorityImplicits {

  implicit def member[T[_[_]], C[_] <: ACopK](
    implicit
      QC: EquiJoin[T, ?] :<<: C): UnicoalesceEJ[T, C] = new UnicoalesceEJ[T, C] {

    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) =
      C.coalesceEJ[C](idPrism.get)
  }
}

sealed trait UnicoalesceTJ[T[_[_]], C[_] <: ACopK] extends Unicoalesce[T, C]

private[qscript] trait UnicoalesceTJLowPriorityImplicits {
  implicit def default[T[_[_]], C[_] <: ACopK]: UnicoalesceTJ[T, C] = new UnicoalesceTJ[T, C] {
    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) = κ(None)
  }
}

object UnicoalesceTJ extends UnicoalesceTJLowPriorityImplicits {

  implicit def member[T[_[_]], C[_] <: ACopK](
    implicit
      QC: ThetaJoin[T, ?] :<<: C): UnicoalesceTJ[T, C] = new UnicoalesceTJ[T, C] {

    def apply(C: Coalesce.Aux[T, C, C])(implicit F: Functor[C]) =
      C.coalesceTJ[C](idPrism.get)
  }
}
