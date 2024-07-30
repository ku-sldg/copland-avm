#!/bin/bash
set -eu

# Function to find dependencies using BFS
find_dependencies_bfs() {
  local file="$1"
  local seen_files=("${@:2}")
  local queue=("$file")
  local seen=()
  local result=()

  while [ ${#queue[@]} -gt 0 ]; do
    # Dequeue the first element
    local current="${queue[0]}"
    queue=("${queue[@]:1}")

    # Check if the file has already been processed or is in the initial seen_files
    if [[ " ${seen[@]} " =~ " ${current} " ]]; then
      # echo -e "SEEN: Already seen $current:\n"
      # We must need to reorder as something in seen depends on current
      # So drop current from past seen and it will be added to front after
      new_array=()
      for val in "${seen[@]}"; do
        [[ $val != $current ]] && new_array+=("$val")
      done
      seen=("${new_array[@]}")
      unset new_array
    fi
    seen=("$current" "${seen[@]}")

    DEP_COM="./pretty_coq_deps.sh $current"
    # Get direct dependencies of the current file
    deps=$($DEP_COM)

    # Add new dependencies to the queue
    for dep in $deps; do
      if [[ " ${dep} " =~ " ${current} " ]]; then
        # echo "SAW CURRENT FILE: $current, $dep"
        continue
      fi
      # Only enqueue if not already seen
      if [[ ! " ${queue[@]} " =~ " ${dep} " ]]; then
        if [[ ! " ${seen[@]} " =~ " ${dep} " ]]; then
          queue+=("$dep")
        else
          # We need to reorder seen as $current depends on $dep still
          queue+=("$dep")
          new_array=()
          for val in "${seen[@]}"; do
            [[ $val != $dep ]] && new_array+=("$val")
          done
          seen=("$dep" "${new_array[@]}")
          unset new_array
        fi
      fi
    done
  done

  # Print the results
  res_str=""
  for file in "${seen[@]}"; do
    if [[ -z "$file" ]]; then
      continue
    fi
    res_str+="$file "
    # echo "$file"
  done
  # res_str=$(printf "%s\n" "${seen[@]}")
  echo "$res_str"
}

# Check if a file is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <file.v> [seen_files...]"
    exit 1
fi

# Get the initial file and seen files
initial_file="$1"
shift
seen_files=("$@")

# Start finding dependencies using BFS
find_dependencies_bfs "$initial_file" "${seen_files[@]}"


