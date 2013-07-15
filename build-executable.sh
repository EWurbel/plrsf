#! /bin/bash

swipl --stand_alone=true --goal="go,halt" --toplevel="halt(1)" -o plrsf -c loader.pl
swipl --stand_alone=true --goal="true" --toplevel="run" -o plrsf-webdemo -c webstarter.pl
echo "==========================================================================="
echo "Compilation terminée,"
echo "l'exécutable en ligne de commande est disponible dans le fichier plrsf,"
echo "l'exécutable de la démo web est disponible dans le fichier plrsf-webdemo."
echo "==========================================================================="

