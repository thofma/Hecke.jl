#!/bin/bash

HECKEDIR="${HOME}/.julia/v0.4/hecke/"

MODULE=$1

docfile=$HECKEDIR"src/"$MODULE"/doc/"$MODULE".text"

rm tmp.tex

cp preamble.tex tmp.tex

echo "Building pdf documentation for module $MODULE ... ";

perl doc.pl --make-latex --file $docfile >> tmp.tex

pdflatex tmp.tex #>/dev/null

#rm tmp.tex

rm tmp.log

rm tmp.aux

mv tmp.pdf doc.pdf

echo "Output written to doc.pdf"
