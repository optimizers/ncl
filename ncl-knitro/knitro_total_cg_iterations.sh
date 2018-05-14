#!/bin/bash

grep '# of CG iterations' $1 | awk '{s+=$NF}END{print s}'
