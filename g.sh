#! /usr/bin/env bash

cargo t
dot -Tpng -O last.dot
open last.dot.png
