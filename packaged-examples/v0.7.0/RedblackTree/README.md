Redblack Tree
-------------

This redblack tree example is taken from Andew W. Appel's [Verified Functional Algorithms (VFA)](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html) e-book. Its syntax has been slightly modified in accordance with Scallina’s coding conventions. The exact changes operated on the code are detailed in the [```Redblack.v```](./Redblack.v) file.

The [```RedblackProof.v```](./RedblackProof.v) file portrays the theorems developed in the VFA e-book which verify that this is a redblack tree. These theorems along with their proofs still hold on the code in the [```Redblack.v```](./Redblack.v) file. The syntax of the [```RedblackProof.v```](./RedblackProof.v) file was slightly adapted to match the changes in the [```Redblack.v```](./Redblack.v) file. The exact syntax adaptations operated on the theorems and proofs are detailed in the [```RedblackProof.v```](./RedblackProof.v) file.

The verified Gallina code in the [```Redblack.v```](./Redblack.v) file can now be translated to Scala using Scallina. The resulting Scala code is exhibited in the [```scallina/Redblack.scala```](scallina/Redblack.scala) file. This file was generated using the [```generate-scala-code.sh```](./generate-scala-code.sh) script. It can be compiled using the [```compile-scala-code.sh```](./compile-scala-code.sh) script.
