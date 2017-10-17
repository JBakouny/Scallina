#!/bin/bash

mkdir -p scallina/;

scala ../scallina-assembly-0.2.jar --uncurrify RedBlack.v > scallina/RedBlack.scala
