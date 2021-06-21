#!/bin/sh
alias LS='ls -l'
alias NIDHUGGC='/home/sarbojit/local/nidhugg/src/nidhuggc -sc -event'
for FILE in *.c
do
  echo "****************************************************************************************************"
  LS $FILE
  NIDHUGGC $FILE
done
