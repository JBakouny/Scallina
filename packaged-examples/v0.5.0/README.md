Scallina's Demonstration
-----------------------

Scallina’s functionalities are demonstrated through the extraction of Scala programs from source Gallina programs. This directory exhibits such extraction examples. Each example includes: the source Gallina code, the lemmas verifying its correctness and the synthesized Scala code.

### Scala Code Generation

Additionally, every example provides a handy Bash script that facilitates the generation of the Scala program from the Coq program by running the below command in its current directory:

```
./generate-scala-code.sh
```

The contents of this script are roughly equivalent to:

```
scala scallina-assembly-${VERSION}.jar ${INPUT_F}.v > ${OUTPUT_F}.scala
```

### Compiling the Generated Scala Code

Once the Scala program is generated, it can be compiled using the below command (that should be run in the same directory as the previous one):

```
./compile-scala-code.sh
```

The contents of this script are roughly equivalent to:

```
scalac -classpath scallina-standard-library-assembly-${VERSION}.jar ${SCALA_CODE_FILE}.scala
```
