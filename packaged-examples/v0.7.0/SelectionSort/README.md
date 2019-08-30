Selection Sort
--------------

This selection sort example is taken from Andew W. Appel's [Verified Functional Algorithms (VFA)](https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html) e-book. Its syntax has been slightly modified in accordance with Scallina’s coding conventions. The exact changes operated on the code are detailed in the [```Selection.v```](./Selection.v) file.

The [```SelectionProof.v```](./SelectionProof.v) file portrays the theorems developed in the VFA e-book which verify that this is a sorting algorithm. These theorems along with their proofs still hold on the code in the [```Selection.v```](./Selection.v) file.

The verified Gallina code in the [```Selection.v```](./Selection.v) file can now be translated to Scala using Scallina. The resulting Scala code is exhibited in the [```scallina/Selection.scala```](scallina/Selection.scala) file. This file was generated using the [```generate-scala-code.sh```](./generate-scala-code.sh) script. It can be compiled using the [```compile-scala-code.sh```](./compile-scala-code.sh) script.
