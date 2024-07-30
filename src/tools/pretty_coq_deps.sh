#!/bin/bash
set -eu

coqdep $1 | 
awk -F ': ' '{print $2}' |
tr ' ' '\n' |
sed 's/\.\///g' |
sed 's/\(\w[\w_]*\)\.\(vio\|vo\)/\1.v/g' |
grep -v '^$'

