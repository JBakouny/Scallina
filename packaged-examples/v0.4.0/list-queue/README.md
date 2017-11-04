List Queue Parametricity
------------------------

This list queue example is taken from the test suite of Coq’s [Parametricity Plugin](https://github.com/parametricity-coq/paramcoq). It has been modified in accordance with Scallina’s coding conventions. The exact changes operated on the code are detailed in the [```ListQueueParam.v```](./ListQueueParam.v) file.

The [```ListQueueProof.v```](./ListQueueProof.v) file contains a proof of the equivalence between the behavior of either `ListQueue` or `DListQueue` when used with ```program```. This proof, which was implemented using Coq’s Parametricity plugin, still holds on the example depicted in the [```ListQueueParam.v```](./ListQueueParam.v) file. The [```How to install the paramcoq plugin.txt```](./How to install the paramcoq plugin.txt) file provides instructions on how to install the Parametricity plugin in order to run this machine-checkable proof.

The verified Gallina code in the [```ListQueueParam.v```](./ListQueueParam.v) file was translated to Scala using Scallina. The resulting Scala code is exhibited in the [```scallina/ListQueueParam.scala```](scallina/ListQueueParam.scala) file. This file was generated using the [```generate-scala-code.sh```](./generate-scala-code.sh) script.
