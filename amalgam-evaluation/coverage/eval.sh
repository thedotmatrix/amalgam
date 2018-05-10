sname="$1"
shift
fname="$1"
shift
mkdir -p data/$fname
time ./runner EvaluationCLI $sname --out data/$fname "$@"
diff data/$fname/blind.txt data/$fname/normal.txt
