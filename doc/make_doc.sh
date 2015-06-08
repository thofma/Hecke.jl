#!/bin/bash

rm tmp.tex

cp preamble.tex tmp.tex

perl doc.pl >> tmp.tex

latexmk -pdf tmp.tex

latexmk -c

rm tmp.tex

mv tmp.pdf doc.pdf
