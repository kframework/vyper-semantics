#!/usr/bin/env bash
set -e      # Exit immediately if any command fails
set -u      # Using undefined variables is an error. Exit immediately

# get the directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd ${DIR}/..

java -jar lib/test-runner.jar -gen bin/aux_viper_parser_for_test.sh -taskExt py tests

rm -rf .test
