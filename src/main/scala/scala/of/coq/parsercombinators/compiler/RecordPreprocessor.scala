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
  type IsRecordTypeField = Boolean

  def computeConstructorToRecordTypeFields(coqTrees: List[Sentence]): Map[RecordConstructorName, List[IsRecordTypeField]] = {
    for {
      r @ Record(_, Ident(recordName), _, (None | Some(Type)), constructor, fields) <- coqTrees
    } yield (
      computeRecordConstructorName(r) ->
      fields.map(recordFieldIsTypeField)
    )
  }.toMap

  def recordFieldIsTypeField(recordField: RecordField): Boolean =
    recordField match {
      case AbstractRecordField(_, None, Type)                  => true
      case AbstractRecordField(_, _, typeTerm)                 => false
      case ConcreteRecordField(_, _, Some(Type), bodyTypeTerm) => true
      case ConcreteRecordField(_, _, Some(typeTerm), bodyTerm) => false
      case anythingElse =>
        throw new IllegalStateException("This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
    }
  
  def computeRecordConstructorName(record: Record): String = {
    val Record(_, Ident(recordName), _, (None | Some(Type)), constructor, _) = record
    constructor.fold("Build_" + recordName) { case Ident(constructorName) => constructorName }
  }

}
