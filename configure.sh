#!/bin/sh

if [ -n ${COQ_MAKEFILE} ]; then
    ${COQ_MAKEFILE} -f _CoqProject -o Makefile
else
    coq_makefile -f _CoqProject -o Makefile
fi
