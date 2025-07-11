import re

# List your global variables here (add/remove as needed)
global_vars = [
    'APP_VAL', 'n', 'm', 'seedSet', 'origNumNodes', 'numNodes', 'numArcs',
    'source', 'sink', 'numParams', 'lastInternalArc', 'weightedEdges',
    'lowestStrongLabel', 'highestStrongLabel', 'weightedNodes', 'sourceSetSize',
    'initialVolumeComplement', 'readTime', 'initTime', 'solveTime', 'injectedLambda',
    'isLambdaInjected', 'currLambda', 'TOL', 'totDegreeSourceSet', 'totWeightSourceSet',
    'numRelabels', 'numPushes', 'numMergers', 'numGaps', 'numArcScans',
    'arcList', 'adjacencyList', 'labelCount', 'inSourceSet', 'bestSourceSet',
    'mapping', 'invMapping', 'nodeWeights', 'edgeWeights', 'partition'
]

with open("incremental.c", "r") as f:
    code = f.read()

# Replace each variable as a word boundary, with (p->var)
for var in sorted(global_vars, key=len, reverse=True):  # Longest first to avoid partial matches
    # Only match the variable name as a whole word
    pattern = rf'\b{var}\b'
    code = re.sub(pattern, f'(p->{var})', code)

with open("incremental_global_replace.c", "w") as f:
    f.write(code)

print("Done! Check 'incremental_global_replace.c' for the result.")

