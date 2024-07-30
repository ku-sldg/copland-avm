#!/bin/bash

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
    # echo -e "Running Queue: \n${queue[@]}\n"
    # echo -e "Running Seen: \n${seen[@]}\n"

    # echo -e "Finding dependencies for $current\n"

    # Check if the file has already been processed or is in the initial seen_files
    if [[ " ${seen[@]} " =~ " ${current} " ]]; then
      # echo -e "SEEN: Already seen $current:\n"
      # We must need to reorder as something in seen depends on current
      # So drop current from past seen and it will be added to front after
      seen=("${seen[@]/$current}")
    fi
      #  in ${seen[@]}\n"
      # Reorder the seen list to put the current file at the front
      # seen=("$current" "${seen[@]/$current}")
      #continue
    #fi 
    # Mark the current file as seen
    seen=("$current" "${seen[@]}")


	DEP_COM="./pretty_coq_deps.sh $current"
    # Get direct dependencies of the current file
	deps=$($DEP_COM)
	echo $deps
    
    # echo -e "Dependencies: $deps\n"

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
          # echo "Not in queue, but in seen, so must be already processed: $dep"
          # We need to reorder seen as $current depends on $dep still
          queue+=("$dep")
          seen=("$dep" "${seen[@]/$dep}")
        fi
      # else
        # echo "Already in queue: $dep"
      fi
    done
  done

  # Print the results
  echo "${seen[@]}"
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


