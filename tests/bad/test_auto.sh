#!/bin/bash

rm -f *.s *.dot *.png

liste_a_tester=`ls |rev | cut -c 4- |rev`

for fichier in $liste_a_tester
do
	/home/hazdard/ENS/projet_prog/projet_nanogo/src/ngoc $fichier.go 2>/dev/null && echo $fichier && echo " "
done

rm -f *.s *.dot *.png
