Scallina’ Demonstration
-----------------------

Scallina’s functionalities are demonstrated through the extraction of Scala programs from source Gallina programs. This directory exhibits such extraction examples. Each example includes: the source Gallina code, the lemmas verifying its correctness and the synthesized Scala code.

Additionally, every example provides a handy Bash script that facilitates the generation of the Scala program from the Coq program by running the below command in its current directory:

```
./generate-scala-code.sh
```

The contents of this script are roughly equivalent to:

```
scala scallina-assembly-${VERSION}.jar ${INPUT_F}.v > ${OUTPUT_F}.scala
```
