#!/bin/bash

HECKEDIR="${HOME}/.julia/v0.4/hecke/"

MODULE=$1

rm tmp.jl

cp preamble.tex tmp.tex

docfile=$HECKEDIR"src/"$MODULE"/doc/"$MODULE".text"

echo "Extracting examples of $docfile ..."

perl doc.pl --make-examples --file $docfile > tmp.jl

echo "Examples written to julia file tmp.jl"
echo "Run julia -q tmp.jl if wished"
