#!/bin/bash

ORIGDIR=$(pwd)

TIMESTAMP=$(date +%Y-%m-%d-%H-%M-%S)

RESULTSDIR=$ORIGDIR/output/$TIMESTAMP/results/
LOGDIR=$ORIGDIR/output/$TIMESTAMP/logs/
mkdir -p $RESULTSDIR
mkdir -p $LOGDIR

TESTDIR="/dev/shm/form-bench-$TIMESTAMP/"
mkdir $TESTDIR

TMPDIR=$TESTDIR/formtmp
mkdir $TMPDIR
export FORMTMP=$TMPDIR

cp -r $ORIGDIR/tests/* $TESTDIR
cd $TESTDIR


N=2
declare -A runs
runs["trace"]=$(($N * 30 ))
runs["mincer"]=$(($N * 4 ))
runs["minceex"]=$(($N * 6 ))
runs["mass-fact"]=$(($N * 4 ))
runs["forcer"]=$(($N * 3 ))
runs["forcer-exp"]=$(($N * 4 ))
runs["mbox1l"]=$(($N * 15 ))
runs["color"]=$(($N * 15 ))
runs["chromatic"]=$(($N * 4 ))
declare -A warmup
warmup["trace"]=3
warmup["mincer"]=0
warmup["minceex"]=0
warmup["mass-fact"]=0
warmup["forcer"]=0
warmup["forcer-exp"]=0
warmup["mbox1l"]=1
warmup["color"]=1
warmup["chromatic"]=0


FORM1=tform-test
FORM2=tform-test-ps
CPU=24

#TESTS="trace mincer minceex mass-fact forcer forcer-exp mbox1l color chromatic"
TESTS="trace minceex forcer forcer-exp mbox1l color chromatic"


for test in $TESTS; do
	cd $test
	echo ""
	echo ""
	echo Running $test
	hyperfine --warmup ${warmup[$test]} --runs ${runs[$test]} \
		--export-json $RESULTSDIR/results-$test.json \
		--command-name "$FORM1" \
		--command-name "$FORM2" \
		"nice -n -10 $FORM1 -w$CPU $test.frm > $LOGDIR/$test.log1" \
		"nice -n -10 $FORM2 -w$CPU $test.frm > $LOGDIR/$test.log2"
	cd ..
done


cd $ORIGDIR
rm -rf $TESTDIR

