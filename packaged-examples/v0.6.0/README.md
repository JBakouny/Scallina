Scallina's Demonstration
-----------------------

Scallina’s functionalities are demonstrated through the extraction of Scala programs from source Gallina programs. This directory exhibits such extraction examples. Each example includes: the source Gallina code, the lemmas verifying its correctness and the synthesized Scala code.


### Compiling the Coq Project

The root directory for this version contains a Makefile that should be used to compile the examples all at once before loading any of them in Coq. To do this, run the below command in the current directory:
```
make
```


### Scala Code Generation

Every example provides a handy Bash script that facilitates the generation of the Scala program from the Coq program by running the below command in the directory of the example:

```
./generate-scala-code.sh
```

The contents of this script are roughly equivalent to:

```
scala scallina-assembly-${VERSION}.jar ${INPUT_F}.v > ${OUTPUT_F}.scala
```

### Compiling the Generated Scala Code

Once the Scala program is generated, it can be compiled using the below command (that should also be run in the directory of the example):

```
./compile-scala-code.sh
```

The contents of this script are roughly equivalent to:

```
scalac -classpath scallina-standard-library-assembly-${VERSION}.jar ${SCALA_CODE_FILE}.scala
```
