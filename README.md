# Incremental cut procedure for conductance* Problem

This repository contains an implementation of the incremental cut procedure for the conductance* Problem. The problem is formulated as


$\min_{S \subseteq R} \left[ C(S,\bar{S}) - \lambda~q(S) \right].$

Where $R$ is a subset of the input graph. Note that, if $R$ is the entire graph, then the initial solution is optimal, and has an objective function value of 0.

# Compiling

A makefile is provided. To compile the `incremental` executable, use:

```
mkdir bin
make
```

# Usage

The executable reads the input file from stdin. To execute one of the examples, use:
```
./bin/incremental < examples/example.txt
```

# Input format

The input graph, with ``n`` nodes and ``m`` edges, and the  is to be provided in the following text format:

```
n m R_SIZE ORIG_EDGES_IN_R R_CONNECTED_TO_COMP
1ST_NODE_IN_R
2ND_NODE_IN_R
...
KTH_NODE_IN_R
FROM_EDGE_1 TO_EDGE_1
FROM_EDGE_2 TO_EDGE_2
...
FROM_EDGE_M TO_EDGE_M
```

Where `R_SIZE=K` is the size of the initial subset, `ORIG_EDGES_IN_R` is the number of edges with both its origin and endpoint in `R`, and `R_CONNECTED_TO_COMP` is the number of nodes in `R` that have an edge going to the complement of `R`.

See directory [examples](examples) for sample input files.


