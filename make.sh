#!/bin/env bash

coq_makefile Lib/*.v Src/*.v -f _CoqProject -o Makefile
