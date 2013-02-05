/*
 *  ____    ____    _____    ____    ___     ____ 
 * |  _ \  |  _ \  | ____|  / ___|  / _/    / ___|        Precog (R)
 * | |_) | | |_) | |  _|   | |     | |  /| | |  _         Advanced Analytics Engine for NoSQL Data
 * |  __/  |  _ <  | |___  | |___  |/ _| | | |_| |        Copyright (C) 2010 - 2013 SlamData, Inc.
 * |_|     |_| \_\ |_____|  \____|   /__/   \____|        All Rights Reserved.
 *
 * This program is free software: you can redistribute it and/or modify it under the terms of the 
 * GNU Affero General Public License as published by the Free Software Foundation, either version 
 * 3 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; 
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See 
 * the GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License along with this 
 * program. If not, see <http://www.gnu.org/licenses/>.
 *
 */
package com.precog
package accounts

import com.precog.common.Path
import com.precog.common.cache.Cache
import com.precog.common.security._

import akka.dispatch.{ ExecutionContext, Future, Promise }

import blueeyes.bkka._
import blueeyes.core.data.DefaultBijections._
import blueeyes.core.data.ByteChunk
import blueeyes.core.http._
import blueeyes.core.http.MimeTypes._
import blueeyes.core.http.HttpStatusCodes._
import blueeyes.core.service._
import blueeyes.core.service.engines.HttpClientXLightWeb
import blueeyes.json._
import blueeyes.json.serialization.{ ValidatedExtraction, Extractor, Decomposer }
import blueeyes.json.serialization.DefaultSerialization.{ DateTimeDecomposer => _, DateTimeExtractor => _, _ }
import blueeyes.json.serialization.Extractor._

import org.apache.commons.codec.binary.Base64
import org.joda.time.DateTime
import org.streum.configrity.Configuration
import com.weiglewilczek.slf4s.Logging

import scalaz._
import scalaz.syntax.monad._

case class AccountManagerClientSettings(protocol: String, host: String, port: Int, path: String, user: String, password: String, cacheSize: Int)

trait AccountManagerClientComponent {
  implicit def asyncContext: ExecutionContext
  implicit val M: Monad[Future]

  def accountManagerFactory(config: Configuration): BasicAccountManager[Future] = {
    config.get[String]("service.hardcoded_account").orElse(config.get[String]("service.static_account")).map { accountId =>
      new StaticAccountManager(accountId)(asyncContext)
    }.getOrElse {
      val protocol = config[String]("service.protocol")
      val host = config[String]("service.host")
      val port = config[Int]("service.port")
      val path = config[String]("service.path")
      val user = config[String]("service.user")
      val password = config[String]("service.password")
      val cacheSize = config[Int]("service.cache_size", 1000)

      val settings = AccountManagerClientSettings(protocol, host, port, path, user, password, cacheSize)
      new AccountManagerClient(settings)
    }
  }
}

class AccountManagerClient(settings: AccountManagerClientSettings) extends BasicAccountManager[Future] with AkkaDefaults with Logging {
  import settings._

  private[this] val apiKeyToAccountCache = Cache.simple[APIKey, Set[AccountId]](Cache.MaxSize(cacheSize))

  val asyncContext = defaultFutureDispatch
  implicit val M: Monad[Future] = AkkaTypeClasses.futureApplicative(asyncContext)

  def listAccountIds(apiKey: APIKey) : Future[Set[AccountId]] = {
    apiKeyToAccountCache.get(apiKey).map(Promise.successful(_)).getOrElse {
      invoke { client =>
        client.query("apiKey", apiKey).contentType(application/MimeTypes.json).get[JValue]("") map {
          case HttpResponse(HttpStatus(OK, _), _, Some(jaccounts), _) =>
            jaccounts.validated[Set[WrappedAccountId]] match {
              case Success(accountIds) => {
                val ids = accountIds.map(_.accountId)
                apiKeyToAccountCache.put(apiKey, ids)
                ids
              }
              case Failure(err) =>
                logger.error("Unexpected response to account list request: " + err)
                throw HttpException(BadGateway, "Unexpected response to account list request: " + err)
            }

          case HttpResponse(HttpStatus(failure: HttpFailure, reason), _, content, _) =>
            logger.error("Fatal error attempting to list accounts: " + failure + ": " + content)
            throw HttpException(failure, reason)

          case other =>
            logger.error("Unexpected response from accounts service: " + other)
            throw HttpException(BadGateway, "Unexpected response from accounts service: " + other)
        }
      }
    }
  }

  def mapAccountIds(apiKeys: Set[APIKey]) : Future[Map[APIKey, Set[AccountId]]] =
    apiKeys.foldLeft(Future(Map.empty[APIKey, Set[AccountId]])) {
      case (fmap, key) => fmap.flatMap { m => listAccountIds(key).map { ids => m + (key -> ids) } }
    }

  def findAccountById(accountId: AccountId): Future[Option[Account]] = {
    invoke { client =>
      client.contentType(application/MimeTypes.json).get[JValue](accountId) map {
        case HttpResponse(HttpStatus(OK, _), _, Some(jaccount), _) =>
         jaccount.validated[Option[Account]] match {
           case Success(accounts) => accounts
           case Failure(err) =>
            logger.error("Unexpected response to find account request: " + err)
            throw HttpException(BadGateway, "Unexpected response to find account request: " + err)
         }

        case HttpResponse(HttpStatus(failure: HttpFailure, reason), _, content, _) =>
          logger.error("Fatal error attempting to find account: " + failure + ": " + content)
          throw HttpException(failure, reason)

        case other =>
          logger.error("Unexpected response from accounts service: " + other)
          throw HttpException(BadGateway, "Unexpected response from accounts service: " + other)
      }
    }
  }

  def close(): Future[Unit] = ().point[Future]

  def invoke[A](f: HttpClient[ByteChunk] => A): A = {
    val client = new HttpClientXLightWeb
    val auth = HttpHeaders.Authorization("Basic "+new String(Base64.encodeBase64((user+":"+password).getBytes("UTF-8")), "UTF-8"))
    f(client.protocol(protocol).host(host).port(port).path(path).header(auth))
  }
}
