#!/bin/bash

version=$1;

if [ $# -ne 1 ]; 
    then echo "$0 <Scallina-version>"
    exit 1;
fi


for name in `for f in src/test/resources/*.v; do echo "${f}" | cut -d'.' -f1 | cut -d'/' -f4- ; done`; do scala target/scala-2.12/scallina-assembly-${version}.jar "src/test/resources/${name}.v" > "src/test/resources/scala/of/coq/generated/code/${name}.scala" ; done

