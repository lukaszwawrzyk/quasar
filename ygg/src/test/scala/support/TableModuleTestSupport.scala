/*
 * Copyright 2014–2016 SlamData Inc.
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

package ygg.tests

import scalaz._, Scalaz._
import ygg._, common._, json._, table._, trans._

abstract class TableQspec extends quasar.Qspec {
  outer =>

  val Table  = ygg.table.TableData
  type Table = ygg.table.TableData
  def companion = Table

  protected implicit def liftTableRep(t: Table): TableRep[Table] = t.asRep

  import SampleData._

  def emptyRep: TableRep[Table]                                 = Table.empty.asRep
  def fromJson(values: Seq[JValue]): Table                      = Table.fromJValues(values)
  def fromJson(values: Seq[JValue], sliceSize: Int): Table      = Table.fromJValues(values, sliceSize)
  def fromSample(sampleData: SampleData): Table                 = Table.fromJValues(sampleData.data)
  def fromSample(sampleData: SampleData, blockSize: Int): Table = Table.fromJValues(sampleData.data, blockSize)

  /** Test compat */
  def toJson(table: Table): Need[Stream[JValue]] = Need(table.toJValues)
  def toJsonSeq(table: Table): Seq[JValue]       = table.toVector

  type ASD = Arbitrary[SampleData]

  trait CommuteTest[R, S] {
    def transformR(x: R): R
    def transformS(x: S): S
    def rToS(x: R): S
    def sToR(x: S): R

    def checkOneR(x: R)(implicit ze: Eq[R], zs: Show[R]): MatchResult[R]  = transformR(x) must_= sToR(transformS(rToS(x)))
    def checkR()(implicit za: Arbitrary[R], ze: Eq[R], zs: Show[R]): Prop = prop(checkOneR _)
  }

  class TableCommuteTest(f: EndoA[Seq[JValue]], g: EndoA[Table]) extends CommuteTest[Seq[JValue], Table] {
    def transformR(x: Seq[JValue])  = f(x)
    def transformS(x: Table)        = g(x)
    def rToS(x: Seq[JValue]): Table = fromJson(x)
    def sToR(x: Table): Seq[JValue] = x.toVector
  }

  implicit class SampleDataOps(private val sd: SampleData) {
    def fieldHead = sd.schema.get._2.head._1.head.get
    def fieldHeadName: String = fieldHead match {
      case JPathField(s) => s
      case _             => abort("non-field reached")
    }
    def fieldHeadIndex: Int = fieldHead match {
      case JPathIndex(s) => s
      case _             => abort("non-index reached")
    }
  }

  case class TableTestFun(table: Table, fun: Table => Table, expected: Seq[JValue]) {
    def check(): MatchResult[Seq[JValue]] = (fun(table).toVector: Seq[JValue]) must_=== expected
  }
  case class TableTest(table: Table, spec: TransSpec1, expected: Seq[JValue]) {
    def check(): MatchResult[Seq[JValue]] = ((table transform spec).toVector: Seq[JValue]) must_=== expected
  }
  case class TableProp(f: SampleData => TableTest) {
    def check()(implicit z: ASD): Prop = prop((sd: SampleData) => f(sd).check())
  }

  /** Verify a scalacheck property that for any SampleData generated by the implicit ASD,
   *  generating a table and transforming it with `spec` produces a copoint which is equal
   *  to the result of the function `expect` applied to the original data.
   */
  def checkSpec(spec: TransSpec1)(expect: EndoA[Seq[JValue]])(implicit z: ASD): Prop =
    TableProp(sd => TableTest(fromSample(sd), spec, expect(sd.data))).check()

  def checkCommutes(f: Seq[JValue] => Seq[JValue], g: Table => Table, gen: Gen[Seq[JValue]]): Prop = {
    implicit val za: Arbitrary[Seq[JValue]] = Arbitrary(gen)
    implicit val ze: Eq[Seq[JValue]]        = Eq.equal((x, y) => (x corresponds y)(_ == _))
    implicit val zs: Show[Seq[JValue]]      = Show.shows(_.toString)

    new TableCommuteTest(f, g).checkR()
  }

  def checkSpecDefault(spec: TransSpec1)(expect: EndoA[Seq[JValue]]): Prop =
    checkSpec(spec)(expect)(defaultASD)

  def checkSpecData(spec: TransSpec1, data: Seq[JValue], expected: Seq[JValue]): Prop =
    TableTest(fromJson(data), spec, expected).check()

  def checkTableFun(fun: Table => Table, data: Seq[JValue], expected: Seq[JValue]): Prop = checkTableFun(fun, fromJson(data), expected)
  def checkTableFun(fun: Table => Table, table: Table, expected: Seq[JValue]): Prop      = TableTestFun(table, fun, expected).check()

  def checkSpecDataId(spec: TransSpec1, data: Seq[JValue]): Prop =
    checkSpecData(spec, data, data)

  protected def defaultASD: ASD = sample(schema)

  def sanitize(s: String): String = s.toArray.map(c => if (c < ' ') ' ' else c).mkString("")
}
