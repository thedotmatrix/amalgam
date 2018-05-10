sname="$1"
shift
cat $sname
echo
echo
echo -n "Type the filename: "
read fname
echo -n "Type the command: "
read command
mkdir -p data/$fname
time ./runner EvaluationCLI $sname --out data/$fname --command $command "$@"
diff data/$fname/blind.txt data/$fname/normal.txt
