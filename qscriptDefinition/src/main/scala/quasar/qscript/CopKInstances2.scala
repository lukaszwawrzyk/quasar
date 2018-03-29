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

package iotaz
package internal

import matryoshka.Delay

import scalaz._
import scala.reflect.macros.whitebox.Context
import scala._
import scala.Predef.$conforms
import slamdata.Predef.String
import slamdata.Predef.SuppressWarnings
import slamdata.Predef.Array

@SuppressWarnings(Array("org.wartremover.warts.Null"))
class CopKInstances2(val c: Context) {
  import c.universe._

  private[this] val tb = IotaMacroToolbelt(c)

  private[this] val NatTransName: String = "NaturalTransformation"

  private[this] val NatTransType: Tree = tq"_root_.scalaz.NaturalTransformation"

  private[this] val Delay: Tree = tq"_root_.matryoshka.Delay"
  private[this] val Show: Tree = tq"_root_.scalaz.Show"

  def copkShow[F[a] <: CopK[_, a]](implicit evF: c.WeakTypeTag[F[_]]): c.Expr[Delay[Show, F]] = {
    val tree = q"null.asInstanceOf[Delay[Show, ${evF.tpe}]]"
    c.echo(c.enclosingPosition, showCode(tree))
    c.Expr[Delay[Show, F]](tree)
  }

  /*{
    val F = evF.tpe
    tb.foldAbort[NonEmptyList, Delay[Show, F]](for {
      _ <- guardAssumptions("F", F)
      copK <- tb.destructCopK(F).leftMap(NonEmptyList.one(_))
      tpes <- tb.memoizedTListKTypes(copK.L).leftMap(NonEmptyList.one(_))
    } yield makeShowInstance(F, tpes))
  }*/

  private def makeShowInstance(F: Type, tpes: List[Type]): Tree = {
    val className = TypeName(c.freshName("CopKShow"))
    val FF = toTypeTree(F)
    val A = TypeName("Ξ$")
    val fa = TermName("η$")
    val s = TermName("Δ$")

    val (instanceVals, cases) = tpes.zipWithIndex.map { case (tpe, index) =>
      val valName = TermName(s"showInstance$index")
      val valDefinition = q"private[this] val $valName = _root_.scala.Predef.implicitly[$Delay[$Show, $tpe]]"
      val caseHandler = cq"$index => $valName.apply($fa).show($s.value.asInstanceOf[$tpe[$A]])"
      (valDefinition, caseHandler)
    }.unzip

    val classDefinition = q"""
        class $className extends $Delay[$Show, $FF] {
          ..$instanceVals
          override def apply[$A]($fa: $Show[$A]): $Show[$F] = {
            scalaz.Show.show[$F[$A]] { ($s: $F[$A]) =>
              $s.index match {
                case ..$cases
                case other => throw new _root_.java.lang.Exception(
                  s"iota internal error: index " + other + " out of bounds for " + this)
              }
            }
          }
        }
      """

    val x = q"$classDefinition; new $className"
    c.echo(c.enclosingPosition, showCode(x))
    x
  }

  private[this] def toTypeTree(tpe: Type): Tree = tpe match {
    case poly: PolyType       => projectPoly(poly)
    case TypeRef(_, sym, Nil) => c.internal.gen.mkAttributedIdent(sym)
    case _                    => c.internal.gen.mkAttributedIdent(tpe.typeSymbol)
  }


  /** Converts an eta expanded `PolyType` such as `[z]Either[String, z]`
    * into a type lambda `Tree` `({ type ξ$[z] = Either[String, z] })#ξ$`.
    * The parameter `z` is taken from the original type and used in
    * resulting tree.
    */
  private[this] def projectPoly(tpe: PolyType): Tree = {
    val lambdaName = TypeName("ξ$")
    SelectFromTypeTree(CompoundTypeTree(
      Template(
        q"_root_.scala.AnyRef" :: Nil,
        ValDef(NoMods, termNames.WILDCARD, TypeTree(), EmptyTree),
        TypeDef(NoMods, lambdaName, tpe.typeParams.map(internal.typeDef(_)),
          q"${tpe.resultType}") :: Nil)),
      lambdaName)
  }

  private[this] def guardAssumptions(
    name: String, T: Type
  ): Either[NonEmptyList[String], _] = T.resultType match {
    case _: ExistentialType => Left(NonEmptyList.one(
      s"type parameter $name was inferred to be existential type $T and must be specified"))
    case _ if T =:= typeOf[Nothing] => Left(NonEmptyList.one(
      s"type parameter $name was inferred to be Nothing and must be specified"))
    case _ => Right(())
  }

}
