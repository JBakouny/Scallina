
### What is Scallina ?
- **Foundations:** *[The Scallina Grammar](https://link.springer.com/chapter/10.1007/978-3-030-03044-5_7)*
- **Demonstration:** *[Scallina: Translating Verified Programs from Coq to Scala](https://link.springer.com/chapter/10.1007/978-3-030-02768-1_7)*
- **Video demo:** [available on YouTube](https://youtu.be/-UM-kcYf7jQ).

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

With `--exact-numerics`, `--omit-peano-import` removes the generated `import Nat._` line. Use it only when the generated program compiles without the Peano `Nat` helper; the option does not rewrite uses of that helper or remove other runtime dependencies. The default output is unchanged.

For explicit `From Stdlib Require Import NArith` and `ZArith` sources, exact numeric output also lowers `N.size`, `N.to_nat`, `N.to_uint`, `Z.of_N`, `Z.of_nat`, `Z.to_nat`, `Z.leb`, and `Z.ltb` to `BigInt` operations or checked helpers. The helpers reject negative values where Rocq expects `N` or `nat`; `Z.to_nat` maps negative integers to zero. These conversions do not make arbitrary Rocq libraries extractable: compile the generated Scala with its required language helpers and test the resulting behavior.

With an explicit `From Stdlib Require Import List`, exact numeric output also lowers `repeat`, `firstn`, and `skipn` to helpers that retain `BigInt` counts. Negative counts are rejected; `firstn` and `skipn` handle counts above the list length without narrowing. `repeat` rejects counts above Scala's list capacity before converting to `Int`.

With an explicit `From Stdlib Require Import Decimal`, exact numeric object output imports a structural `Decimal.uint` target with `Nil` and `D0` through `D9` constructors. This represents the inductive's shape for values and pattern matches. `N.to_uint` converts a checked nonnegative `BigInt` through its decimal digits into that structure; the helper's target behavior still needs qualification for each downstream program.
