
### Publications

- **Demonstration:** *[Scallina: Translating Verified Programs from Coq to Scala](https://link.springer.com/chapter/10.1007/978-3-030-02768-1_7)*

- **Foundations:** *[The Scallina Grammar](https://link.springer.com/chapter/10.1007/978-3-030-03044-5_7)*

A video demo is also [available on YouTube](https://youtu.be/-UM-kcYf7jQ).

### Quick start guide

First, download the Scala Build Tool (SBT) from http://www.scala-sbt.org/download.html

Then, in the project's main directory run the command ```sbt assembly```

Finally, the below command:

```scala target/scala-2.12/scallina-assembly-<scallina-version>.jar <path-to-coq-source-file.v>```

can be executed from the project's main directory in order to run Scallina.

Also, the below command should also work:

```java -jar target/scala-2.12/scallina-assembly-<scallina-version>.jar <path-to-coq-source-file.v>```

### Usage Examples

Packaged examples are available under [```packaged-examples```](./packaged-examples)

Additional examples of Coq ```.v``` files that can be translated to Scala are available under [```src/test/resources/```](./src/test/resources/)

### Compiling the Generated Scala Files
The generated files can be compiled with the ```scalac``` Scala compiler provided that the [Scallina Standard Library](https://github.com/JBakouny/Scallina/releases/download/v0.7.0/scallina-standard-library-assembly-0.7.jar) is included in the classpath.

For a practical example, see the ```compile-scala-code.sh``` script in [```packaged-examples/v0.7.0/SelectionSort```](./packaged-examples/v0.7.0/SelectionSort).

The source code of the Scallina Standard Library is available under [```src/main/resources/scala/of/coq/lang```](./src/main/resources/scala/of/coq/lang/).
