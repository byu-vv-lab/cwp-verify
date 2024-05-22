#!/bin/bash

#UNUSED

CEdir=$1

cd ${CEdir}

for i in *; do
    if [[ $i == *.bpmn ]]
    then
        bpmn-to-image $i:$i.png
    fi
done
