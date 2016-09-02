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

import java.lang.SuppressWarnings

@SuppressWarnings(Array("org.wartremover.warts.DefaultArguments"))
object fn {
  def baseUri(node: XQuery): XQuery =
    XQuery(s"fn:base-uri($node)")

  def concat(x: XQuery, xs: XQuery*): XQuery =
    XQuery(s"fn:concat${mkSeq_(x, xs: _*)}")

  def distinctValues(seq: XQuery): XQuery =
    XQuery(s"fn:distinct-values($seq)")

  def doc(): XQuery =
    XQuery("fn:doc()")

  def doc(uri: XQuery): XQuery =
    XQuery(s"fn:doc($uri)")

  def exists(seq: XQuery): XQuery =
    XQuery(s"fn:exists($seq)")

  val False: XQuery =
    XQuery("fn:false()")

  def filter(p: XQuery, seq: XQuery): XQuery =
    XQuery(s"fn:filter($p, $seq)")

  val last: XQuery =
    XQuery("fn:last()")

  def map(f: XQuery, seq: XQuery): XQuery =
    XQuery(s"fn:map($f, $seq)")

  def not(bool: XQuery): XQuery =
    XQuery(s"fn:not($bool)")

  def QName(localPart: XQuery): XQuery =
    XQuery(s"fn:QName($localPart)")

  def QName(namespace: XQuery, localPart: XQuery): XQuery =
    XQuery(s"fn:QName($namespace, $localPart)")

  def startsWith(str: XQuery, prefix: XQuery, collation: Option[XQuery] = None): XQuery =
    XQuery(s"fn:starts-with($str, ${prefix}${asArg(collation)})")

  def stringLength(str: XQuery): XQuery =
    XQuery(s"fn:string-length($str)")

  def substring(str: XQuery, startLoc: XQuery, length: Option[XQuery] = None): XQuery =
    XQuery(s"fn:substring($str, ${startLoc}${asArg(length)})")

  def substringAfter(input: XQuery, after: XQuery): XQuery =
    XQuery(s"fn:substring-after($input, $after)")

  def subsequence(srcSeq: XQuery, startLoc: XQuery, length: Option[XQuery] = None): XQuery =
    XQuery(s"fn:subsequence($srcSeq, ${startLoc}${asArg(length)})")

  def tokenize(input: XQuery, pattern: XQuery, flags: Option[XQuery] = None): XQuery =
    XQuery(s"fn:tokenize($input, ${pattern}${asArg(flags)})")

  val True: XQuery =
    XQuery("fn:true()")
}