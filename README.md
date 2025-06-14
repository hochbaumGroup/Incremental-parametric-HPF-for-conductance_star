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

The executable is run with the following syntax:

```
./bin/incremental graphfile partition_file [OPTIONS]
```

- `graphfile`: path to the input graph in METIS format
- `partition_file`: path to the initial partition file
- `OPTIONS`: optional flags and arguments that customize the execution

You can use the `--help` flag to display the list of available options:

```
./bin/incremental --help
```

This command prints a summary of available options and usage instructions.



# Input Format

The input to this software consists of a graph in **METIS format** and an accompanying initial partition file. The graph has `n` nodes and `m` edges, and is stored as an adjacency list. Each undirected edge appears **twice** in the input—once for each endpoint. The file may include optional **node weights** and **edge weights**, depending on the format specification:

```
n m FORMAT
[WEIGHT_NODE_1] NEIGHBOR_1_NODE_1 [WEIGHT_EDGE_1_NODE_1] NEIGHBOR_2_NODE_1 [WEIGHT_EDGE_2_NODE_1] ...
[WEIGHT_NODE_2] NEIGHBOR_1_NODE_2 [WEIGHT_EDGE_1_NODE_2] NEIGHBOR_2_NODE_2 [WEIGHT_EDGE_2_NODE_2] ...
...
[WEIGHT_NODE_n] NEIGHBOR_1_NODE_n ...
```

- `n`: number of nodes
- `m`: number of undirected edges (each appears twice)
- `FORMAT`: an integer specifying the presence of weights:
  - `0`: no weights
  - `1`: edge weights only
  - `10`: node weights only
  - `11`: both node and edge weights

Each line after the header corresponds to a node’s adjacency list.  \
If node weights are included, the line starts with a weight value.  \
If edge weights are included, each neighbor is followed by the corresponding edge weight.

### Partition File Format

The partition file specifies an initial partition of the graph’s nodes. It follows the format used by METIS output: a plain text file with one line per node. Each line contains either a `0` or a `1`, indicating the partition assignment of the corresponding node:

```
0
1
0
...
```

The node on line `i` belongs to partition `0` or `1`, depending on the value written on that line.





