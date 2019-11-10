# usage: ./select-def *.v
#    builds a file named def.txt holding all definitions and theorems;
#    then we can use ./def-nb-use.sh to count the number of occurrences

cat $@ | egrep '(Theorem|Lemma|Definition|Inductive|Fixpoint)' | sed -e 's/Theorem //; s/Lemma //;s/Definition //;s/Inductive //; s/Fixpoint //;s/(\*.*$//;s/ .*$//' | LC_ALL=C sort | LC_ALL=C uniq > def.txt
