#!/bin/bash

if [ "$#" -ne 2 ]; then
  echo "verify <example-dir> <output-dir>"
  exit 1
fi

if [ ! -d "$1" ]; then
  echo "$1 must be a directory"
  exit 2
fi

if [ ! -d "$2" ]; then
  echo "$2 must be a directory"
  exit 3
fi

example_path=`(cd $1; pwd)`
output_path=`(cd $2; pwd)`

base="$(basename $example_path)"
example_volume="$example_path:/opt/bpmn-cwp-verification/code/assets/examples/$base"
output_volume="$output_path:/opt/bpmn-cwp-verification/code/output/examples/"
docker run --rm -it -v "$example_volume" -v "$output_volume" cwp-bpmn -e $base
