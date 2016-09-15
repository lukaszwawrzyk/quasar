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

package quasar.physical.marklogic.xquery

import quasar.Predef._
import quasar.physical.marklogic.xquery.syntax._

import eu.timepit.refined.auto._

object json {
  val js = module("json", "http://marklogic.com/xdmp/json", "/MarkLogic/json/json.xqy")

  def isObject(node: XQuery): XQuery =
    xdmp.nodeKind(node) === "object".xs

  def transformFromJson[F[_]: PrologW](jsonNode: XQuery): F[XQuery] =
    js("transform-from-json") apply (jsonNode)
}
