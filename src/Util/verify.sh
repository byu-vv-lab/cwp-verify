#!/bin/bash

exName=$1
flags=$2
#Change project directory accordingly
projectDir="/opt/bpmn-cwp-verification"
green=$(tput setaf 2)
red=$(tput setaf 1)
clear=$(tput sgr0)

outDir="${projectDir}/code/output/examples/${exName}"
assetDir="${projectDir}/code/assets/examples/${exName}"


resultsFile="${outDir}/results.txt"
if [ -f "$resultsFile" ] ; then
  rm $resultsFile
fi
argFile="${assetDir}/properties.txt"
spinFile="${outDir}/model.pml"
counterExampleDir="${outDir}/counterExamples"
error=0
expected=0

args=$(< ${argFile})
for i in $args
  do
    printf "%-30s" $i | tee -a $resultsFile
    #Check if property is existential
    case $i in
      *Exists*)
        expected=1
        printf "%-25s" "Errors Expected" | tee -a $resultsFile
      ;;
      *)
        expected=0
        printf "%-25s" "No Errors Expected" | tee -a $resultsFile
      ;;
    esac
    startTime=`date +%s.%N`
    result=`spin -run ${flags} -ltl ${i} ${spinFile} 2>/dev/null`
    endTime=`date +%s.%N`
    runTime=$( echo "$endTime - $startTime" | bc -l )
    states=`echo $result | perl -lne 'print $1 if /(\d+)(?= states, stored)/'`
    transitions=`echo $result | perl -lne 'print $1 if /(\d+)(?= transitions)/'`
    memory=`echo $result | perl -lne 'print $1 if /(\d+\.\d+)(?= equivalent memory usage for states)/'`
    totalMemory=`echo $result | perl -lne 'print $1 if /(\d+\.\d+)(?= total actual memory usage)/'`
    if echo $result | grep -q "errors: 0"
    then
      error=0
      printf "%-25s" "No Errors Found." | tee -a $resultsFile
    else
      error=1
      printf "%-25s" "Errors Found." | tee -a $resultsFile
    fi
    if [ $error = $expected ]
    then
      printf "%-20s" "${green}PASSED"
      printf "%-20s" "PASSED" >> $resultsFile
      printf "${clear}"
    else
      printf "%-20s" "${red}FAILED"
      printf "%-20s" "FAILED" >> $resultsFile
      printf "${clear}"
      if [ $expected = 0 ]
      then
        mkdir "${counterExampleDir}/${i}"
        mv model.pml.trail "${outDir}/model.pml.trail"
        spin -t ${spinFile} > "${counterExampleDir}/${i}/trail.txt"
      fi
    fi

    printf "%-20s" "States: $states" | tee -a $resultsFile
    printf "%-30s" "Transitions: $transitions" | tee -a $resultsFile
    printf "%-25s" "Memory: $memory" | tee -a $resultsFile
    printf "%s%-20.2f" "Runtime: " $runTime | tee -a $resultsFile
    printf "\n" | tee -a $resultsFile
done
