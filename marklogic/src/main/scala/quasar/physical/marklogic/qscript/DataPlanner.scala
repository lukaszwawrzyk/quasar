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

package quasar.physical.marklogic.qscript

import slamdata.Predef._

import quasar.Data
import quasar.physical.marklogic.optics._
import quasar.physical.marklogic.xquery._
import quasar.physical.marklogic.xquery.syntax._

import matryoshka._
import scalaz._, Scalaz._

private[qscript] object DataPlanner {

  @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
  def apply[M[_]: Monad, FMT](data: Data)(implicit SP: StructuralPlanner[M, FMT]): M[XQuery] =
    data match {
      case Data.Binary(bytes) => xs.base64Binary(base64Bytes(bytes).xs).point[M]
      case Data.Bool(b)       => b.fold(fn.True, fn.False).point[M]
      case Data.LocalDate(d)  => xs.date(d.toString.xs).point[M]
      case Data.OffsetDate(d)  => xs.date(d.toString.xs).point[M]
      case Data.LocalDateTime(ts)  => xs.dateTime(ts.toString.xs).point[M]
      case Data.OffsetDateTime(ts) => xs.dateTime(ts.toString.xs).point[M]
      case Data.Dec(d)        => xs.double(d.toString.xqy).point[M]
      case Data.Id(id)        => id.xs.point[M]
      case Data.Int(i)        => xs.integer(i.toString.xqy).point[M]
      case Data.Interval(d)   => xs.duration(isoDuration(d).xs).point[M]
      case Data.NA            => expr.emptySeq.point[M]
      case Data.Null          => SP.null_
      case Data.Str(s)        => s.xs.point[M]
      case Data.OffsetTime(t) => xs.time(t.toString.xs).point[M]
      case Data.LocalTime(t)  => xs.time(t.toString.xs).point[M]

      case Data.Arr(elements) =>
        elements.traverse(Kleisli(apply[M, FMT]) >==> SP.mkArrayElt _) >>= (xs => SP.mkArray(mkSeq(xs)))

      case Data.Obj(entries)  =>
        entries.toList.traverse { case (key, value) =>
          apply[M, FMT](value) >>= (SP.mkObjectEntry(key.xs, _))
        } >>= (ents => SP.mkObject(mkSeq(ents)))

      case _ => apply[M, FMT](data)
    }
}
