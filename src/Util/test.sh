#!/bin/bash

result=`echo "234"`
echo $result
subResult=`echo $result | perl -ne 'print $1 if /(\d+)(?=4)/'`
echo $subResult
if echo $result | grep -q "1"
then
    printf "success\n"
else
    printf "failure\n"
fi

startTime=`date +%s.%N`
sleep 1
endTime=`date +%s.%N`
runTime=$( echo "$endTime - $startTime" | bc -l )

printf "%s%f" "runtime: " $runTime
