#!/usr/bin/env bash

SCRIPT_DIR=`dirname $(python -c "import os, sys; print(os.path.realpath(\"$0\"))")`
SEMTANTICS_DIR=$(dirname $(dirname ${SCRIPT_DIR}))/vyper-lll

test_count=0

run_tests() {
    local tests_dir=$1
    echo "entering ${tests_dir}"

    for f in ${tests_dir}/*.ast
    do
        file_name=${f##*/}
        expected_out=${f/%.ast/.ast.out}
        echo "running ${file_name}"
        test_count=$(($test_count + 1))
        krun $f --output nowrap --debug -d ${SCRIPT_DIR} | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | sed 's/ , .LLLExps//g' > /tmp/vyper.txt
        diff /tmp/vyper.txt ${expected_out}
    done
}

echo "kompile ${SEMTANTICS_DIR}/vyper-lll.k"
kompile ${SEMTANTICS_DIR}/vyper-lll.k --syntax-module VYPER-ABSTRACT-SYNTAX --debug -d ${SCRIPT_DIR}

#parser/features
TESTS_DIR=${SCRIPT_DIR}/parser/features/arithmetic/test_modulo
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/iteration/test_break
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/iteration/test_for_in_list
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/test_assignment
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/test_conditionals
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/test_internal_call
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/features/test_logging
run_tests $TESTS_DIR

#parser/functions
TESTS_DIR=${SCRIPT_DIR}/parser/functions/test_send
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/functions/test_slice
run_tests $TESTS_DIR

#parser/syntax
TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_as_num256
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_for_range
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_list
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_public
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_selfdestruct
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/syntax/test_struct
run_tests $TESTS_DIR

#parser/types
TESTS_DIR=${SCRIPT_DIR}/parser/types/numbers/test_decimals
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/types/numbers/test_num
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/types/numbers/test_num256
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/types/test_bytes
run_tests $TESTS_DIR

TESTS_DIR=${SCRIPT_DIR}/parser/types/test_string_literal
run_tests $TESTS_DIR

#examples
TESTS_DIR=${SCRIPT_DIR}/../examples/token
run_tests $TESTS_DIR

echo "total tests: ${test_count}"
