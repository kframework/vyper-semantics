#!/usr/bin/env bash
trap 'exit' ERR     # Exit immediately if any command fails (better than 'set -e')
set -u              # Using undefined variables is an error. Exit immediately

# get the directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd ${DIR}

java -jar test-runner.jar -gen aux_viper_parser_for_test.sh -taskExt py ../

rm -rf .test
