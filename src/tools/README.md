# Tools

The following tools exist as general purpose tools
that could be used in a Coq development.

- [find_all_deps](./find_all_deps.sh): This tool takes a single argument (the name of a Coq .v file) and returns an ordered list of the dependencies it **recursively** relies on.

- [pretty_coq_deps](./pretty_coq_deps.sh): This tool takes a single argument (the name of a Coq .v file) and returns a list of the 
dependencies it relies on **non-recursively**.

- [test_all_files](./test_all_files.sh): This is just a testing tool for checking and validating the dependencies of all files in a directory (passed as the only argument)

- [validate_all_deps](./validate_all_deps.sh): This tool takes an ordered list of dependencies and validates that each file in that list only depends on files that have previously appear in the list. Basically it is the dual of *find_all_deps*.