#!/usr/bin/env bash
trap 'exit' ERR     # Exit immediately if any command fails (better than 'set -e')
set -u              # Using undefined variables is an error. Exit immediately

# get the directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

python3 ${DIR}/../../scripts/viper_parser.py $1
