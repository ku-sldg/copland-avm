#!/bin/bash
set -eu

files_list=($(cat))
len=${#files_list[@]}
echo "Files list: ${files_list[@]}"

# For file in files_list, ensure that $deps is only made of files
# from the previous elements of files_list
for((i=0; i<$len; i++)); do
  cur_slice=("${files_list[@]:0:($i + 1)}")
  cur_value=${files_list[$i]}

  # Get direct dependencies of the current file
  DEP_COM="./pretty_coq_deps.sh $cur_value"
  deps=$($DEP_COM)

  # Check if all dependencies are in previous files_list
  for dep in $deps; do
    if [[ ! " ${cur_slice[@]} " =~ " ${dep} " ]]; then
      echo "ERROR: $dep not in previous files_list"
      exit 1
    fi
  done
done
