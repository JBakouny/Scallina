package scala.of.coq.parsercombinators.compiler

import scala.of.coq.parsercombinators.parser.Record
import scala.of.coq.parsercombinators.parser.Sentence
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.Set
import scala.of.coq.parsercombinators.parser.AbstractRecordField
import scala.of.coq.parsercombinators.parser.ConcreteRecordField
import scala.of.coq.parsercombinators.parser.RecordField

object RecordPreprocessor {
  type RecordConstructorName = String
  type IsRecordTypeField = Boolean

  def computeConstructorToRecordTypeFields(coqTrees: List[Sentence]): Map[RecordConstructorName, List[IsRecordTypeField]] = {
    for {
      Record(_, Ident(recordName), _, (None | Some(Set | Type)), Some(Ident(constructorName)), fields) <- coqTrees
    } yield (
      constructorName ->
      fields.map(recordFieldIsTypeField))
  }.toMap

  def recordFieldIsTypeField(recordField: RecordField): Boolean =
    recordField match {
      case AbstractRecordField(_, _, Set | Type)                     => true
      case AbstractRecordField(_, _, typeTerm)                       => false
      case ConcreteRecordField(_, _, Some(Set | Type), bodyTypeTerm) => true
      case ConcreteRecordField(_, _, Some(typeTerm), bodyTerm)       => false
      case anythingElse @ ConcreteRecordField(_, _, None, bodyTerm) =>
        throw new IllegalStateException("This record field should have an explicit return type: " + anythingElse.toCoqCode)
      case anythingElse =>
        throw new IllegalStateException("This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
    }
}
