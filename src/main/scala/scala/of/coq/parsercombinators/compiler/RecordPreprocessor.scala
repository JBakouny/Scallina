package scala.of.coq.parsercombinators.compiler

import scala.of.coq.parsercombinators.parser.Record
import scala.of.coq.parsercombinators.parser.Sentence
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.AbstractRecordField
import scala.of.coq.parsercombinators.parser.ConcreteRecordField
import scala.of.coq.parsercombinators.parser.RecordField

object RecordPreprocessor {
  type RecordConstructorName = String
  type IsRecordTypeField     = Boolean

  def computeConstructorToRecordTypeFields(
      coqTrees: List[Sentence]
  ): Map[RecordConstructorName, List[IsRecordTypeField]] = {
    for {
      Record(_, Ident(_), _, None | Some(Type), Some(Ident(constructorName)), fields) ← coqTrees
    } yield
      constructorName →
        fields.map(recordFieldIsTypeField)
  }.toMap

  def recordFieldIsTypeField(recordField: RecordField): Boolean =
    recordField match {
      case AbstractRecordField(_, None, Type)       ⇒ true
      case AbstractRecordField(_, _, _)             ⇒ false
      case ConcreteRecordField(_, _, Some(Type), _) ⇒ true
      case ConcreteRecordField(_, _, Some(_), _)    ⇒ false
      case anythingElse ⇒
        throw new IllegalStateException("This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
    }
}
