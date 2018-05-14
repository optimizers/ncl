#!/bin/bash

grep '# of iterations' $1 | awk 'BEGIN{k=1; printf "%5s  %5s\n", "outer", "inner"}{printf "%5d  %d\n", k, $NF; k += 1; s += $NF}END{printf "%5s  %d\n", "total", s}'
