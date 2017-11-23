#!/usr/bin/env bash

SCRIPT_DIR=`dirname $(python -c "import os, sys; print(os.path.realpath(\"$0\"))")`
SEMTANTICS_DIR=`dirname $SCRIPT_DIR`/viper-lll

echo "kompile viper-lll"
kompile $SEMTANTICS_DIR/viper-lll.k --syntax-module VIPER-ABSTRACT-SYNTAX --debug -d $SCRIPT_DIR

echo "running tests/features/test_assignment/test_assignment.v"
krun $SCRIPT_DIR/features/test_assignment/test_assignment.v --output nowrap --debug -d $SCRIPT_DIR | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | sed 's/ , .LLLExps//g' > /tmp/viper.txt
diff /tmp/viper.txt $SCRIPT_DIR/features/test_assignment/test_assignment.v.out

echo "running tests/features/test_conditionals/test_conditional_return_code.v"
krun $SCRIPT_DIR/features/test_conditionals/test_conditional_return_code.v --output nowrap --debug -d $SCRIPT_DIR | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | sed 's/ , .LLLExps//g' > /tmp/viper.txt
diff /tmp/viper.txt $SCRIPT_DIR/features/test_conditionals/test_conditional_return_code.v.out

echo "running tests/examples/token/ERC20.v"
krun $SCRIPT_DIR/examples/token/ERC20.v --output nowrap --debug -d $SCRIPT_DIR | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | sed 's/ , .LLLExps//g' > /tmp/viper.txt
diff /tmp/viper.txt $SCRIPT_DIR/examples/token/ERC20.v.out
