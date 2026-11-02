package scala.of.coq.parsercombinators
import org.scalatest.FunSuite
import org.scalatest.Matchers
import scala.of.coq.parsercombinators.parser.CoqParser
import scala.util.parsing.input.OffsetPosition

class SourceReaderTest extends FunSuite with Matchers {
  test("scanner positions retain the immutable source string") {
    val source = "Definition identity (n : nat) := n.\n"
    val position = CoqParser.scannerFor(source).pos.asInstanceOf[OffsetPosition]
    position.source shouldBe a[String]
    position.source.asInstanceOf[AnyRef] should be theSameInstanceAs source
  }
  test("scanner advances preserve immutable input and line positions") {
    val source = "Definition first := 1.\nDefinition second := 2."
    var scanner = CoqParser.scannerFor(source)
    while (!scanner.atEnd) {
      val position = scanner.pos.asInstanceOf[OffsetPosition]
      position.source shouldBe a[String]
      position.source.asInstanceOf[AnyRef] should be theSameInstanceAs source
      scanner = scanner.rest.asInstanceOf[CoqParser.lexical.Scanner]
    }
    scanner.pos.line shouldBe 2
  }
}
