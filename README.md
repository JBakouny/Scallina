
### Publications

- **Introduction:** *[A Coq-based synthesis of Scala programs which are correct-by-construction](http://dl.acm.org/citation.cfm?doid=3103111.3104041)* ([Direct link to the PDF](https://cedric.cnam.fr/fichiers/art_4027.pdf))

- **Demonstration:** *[Scallina: Translating Verified Programs from Coq to Scala](https://link.springer.com/chapter/10.1007/978-3-030-02768-1_7)* ([Direct link to google book extract](https://books.google.fr/books?id=kmF7DwAAQBAJ&pg=PA130))

- **Foundations:** *[The Scallina Grammar](https://link.springer.com/chapter/10.1007/978-3-030-03044-5_7)* ([Direct link to google book extract](https://books.google.fr/books?id=QM96DwAAQBAJ&pg=PA90))

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
The generated files can be compiled with the ```scalac``` Scala compiler provided that the [Scallina Standard Library](./packaged-examples/v0.5.0/scallina-standard-library-assembly-0.5.jar) is included in the classpath.

For a practical example, see the ```compile-scala-code.sh``` scripts in [```packaged-examples/v0.5.0/list-queue/```](./packaged-examples/v0.5.0/list-queue/) and [```packaged-examples/v0.5.0/selection-sort/```](./packaged-examples/v0.5.0/selection-sort/).

The source code of the Scallina Standard Library is available under [```src/main/resources/scala/of/coq/lang```](./src/main/resources/scala/of/coq/lang/).
