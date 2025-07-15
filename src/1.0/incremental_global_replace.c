#include <stdio.h>
#include <math.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <stdlib.h>
#include <string.h>

typedef enum
{
    READ_OK,     // Integer successfully read
    READ_EOL,    // End of line encountered before integer
    READ_EOF,    // End of file reached
    READ_FAIL    // Failed to read integer (malformed input)
} readReturn;


size_t getLine(char **linePtr, size_t *n, FILE *stream)
{
    if (!linePtr || !n || !stream)
        return (size_t)-1;

    if (*linePtr == NULL || n == 0) {
        *n = 128;
        *linePtr = malloc(*n);
        if (!*linePtr) return (size_t)-1;
    }

    size_t len = 0;
    size_t newSize = 0;
    
    char *tmp = NULL;

    while (1)
    {
        if (fgets(*linePtr + len, *(n) - len, stream) == NULL)
        {
            if (len == 0) return (size_t)-1; // Nothing read
            break; // Partial line read before EOF
        }

        len += strlen(*linePtr + len);

        // If newline was read, we're done
        if (len > 0 && (*linePtr)[len - 1] == '\n')
            break;

        // Otherwise, line is too long — need to grow buffer
        newSize = *(n) * 2;
        tmp = realloc(*linePtr, newSize);
        if (!tmp) return (size_t)-1;

        *linePtr = tmp;
        *(n) = newSize;
    }

    return len;
}



typedef long long int llint;

void swap(int *a, int *b)
{
	int c = *a;
	*a = *b;
	*b = c;
}


int readInt()
{
  int res = 0;
  char c = getchar_unlocked();
  while( c < '0' || c > '9' )
  {
    c = getchar_unlocked();
  }

  while ( c >= '0' )
  {
    res = res*10 + (c - '0');
    c = getchar_unlocked();
  }
  return res;
}


int readLL()
{
  long long res = 0;
  char c = getchar_unlocked();
  while( c < '0' || c > '9' )
  {
    c = getchar_unlocked();
  }

  while ( c >= '0' )
  {
    res = res*10LL + (long long)(c - '0');
    c = getchar_unlocked();
  }
  return res;
}

static char *
getNextWord (char *line, char *word)
{
  int wordlength = 0;

  while (((*line) == ' ') || ((*line) == '\t') || ((*line) == '\n') || ((*line) == '\0'))
  {
    ++ line;
  }

  while (((*line) != ' ') && ((*line) != '\t') && ((*line) != '\n') && ((*line) != '\0'))
  {
    word[wordlength] = (*line);
    ++ wordlength;
    ++ line; 
  }
  
  word[wordlength] = '\0';
  return line;
}

double
fmax(double a, double b)
{
  return (a>b) ? a : b;
}

double
fmin(double a, double b)
{
  return (a<b) ? a : b;
}

int 
max(int a, int b)
{
  return (a>b) ? a : b;
}

int 
min(int a, int b)
{
  return (a<b) ? a : b;
}


long long 
lmax(long long a, long long b)
{
  return (a>b) ? a : b;
}

long long 
lmin(long long a, long long b)
{
  return (a<b) ? a : b;
}

long long
ceil_div(long long a, long long b)
{
  //return (a+b-1LL)/b;
	long long res = a/b;
	if(a%b) res++;
	return res;	
}

static double 
timer (void)
{
  struct rusage r;

  getrusage(0, &r);
  return (double) (r.ru_utime.tv_sec + r.ru_utime.tv_usec / (double)1000000);
}

struct node;

typedef struct arc 
{
  long long flow;
  long long  capacity;
  long long intercept;
  long long slope;
  int from;
  int to;
  char direction;
} Arc;

typedef struct node 
{
  struct node *parent;
  struct node *childList;
  struct node *nextScan;
  struct node *next;
  struct node *prev;
  Arc **outOfTree;
  Arc *arcToParent;
  long long excess;
  long long breakpoint;
  int numOutOfTree;
  int nextArc;
  int visited;
  int numAdjacent;
  int label;
} Node;


typedef struct root 
{
  Node *start;
  Node *end;
} Root;

// edge of the original graph
typedef struct edge
{
  int u;
  int v;
  int w;
} Edge;

//---------------  Global variables ------------------
typedef struct CutProblem_
{
  long long APP_VAL;
  long long n;
  long long m;
  int seedSet;
  int origNumNodes;
  int numNodes;
  int numArcs;
  int source;
  int sink;
  int numParams;
  int lastInternalArc;
  int weightedEdges;
  uint lowestStrongLabel;
  uint highestStrongLabel;
  int weightedNodes;
  int sourceSetSize;
  long long initialVolumeComplement;

  double readTime;
  double initTime;
  double solveTime;
   
  double injectedLambda;
  char isLambdaInjected;
   
  long long currLambda;


  Node *adjacencyList;
  Root *strongRoots;
  int *labelCount;
  Arc *arcList;
  Edge *edges;

  int *orEdges;
  int *invMapping;
  char *inOrigS;
  int *origDeg;

  double TOL;
  double totDegreeSourceSet;
  double totWeightSourceSet;

  int *degrees;
  int *adjacents;
  int *value;
  int *weights;
  char *inSourceSet;
  char *bestSourceSet;
  int *edgeEnd;
  int *firstEdge;

  FILE *dumpSourceSetFile;
  //-----------------------------------------------------

  long long numRelabels;
#ifdef STATS
  llint numPushes;
  int numMergers;
  int numGaps;
  llint numArcScans;
#endif
} CutProblem;

void
defaultInitializeProblem (CutProblem *p)
{
  (p->APP_VAL) = 1000000LL;
  (p->n) = 0;
  (p->m) = 0;
  (p->seedSet) = 0;
  (p->origNumNodes) = 0;
  (p->numNodes) = 0;
  (p->numArcs) = 0;
  (p->source) = 0;
  (p->sink) = 0;
  (p->numParams) = 0;
  (p->lastInternalArc) = 0;
  (p->weightedEdges) = 0;
  (p->lowestStrongLabel) = 1;
  (p->highestStrongLabel) = 1;
  (p->weightedNodes) = 0;
  (p->sourceSetSize) = 1;
  (p->initialVolumeComplement) = 0;

  (p->readTime) = 0.0f;
  (p->initTime) = 0.0f;
  (p->solveTime) = 0.0f;
   
  (p->injectedLambda) = 1e9;
  (p->isLambdaInjected) = 0;
   
  (p->currLambda) = 0;


  (p->adjacencyList) = NULL;
  p->strongRoots = NULL;
  (p->labelCount) = NULL;
  (p->arcList) = NULL;
  p->edges = NULL;

  p->orEdges = NULL;
  (p->invMapping) = NULL;
  p->inOrigS = NULL;
  p->origDeg = NULL;

  (p->TOL) = 1e-5;
  (p->totDegreeSourceSet) = 0.0;
  (p->totWeightSourceSet) = 0.0;

  p->degrees = NULL;
  p->adjacents = NULL;
  p->value = NULL;
  p->weights = NULL;
  (p->inSourceSet) = NULL;
  (p->bestSourceSet) = NULL;
  p->edgeEnd = NULL;
  p->firstEdge = NULL;

  p->dumpSourceSetFile = NULL;
  //-----------------------------------------------------

  (p->numRelabels) = 0;
#ifdef STATS
  (p->numPushes) = 0;
  (p->numMergers) = 0;
  (p->numGaps) = 0;
  (p->numArcScans) = 0;
#endif

}

static long long
computeValuesLastPartition(CutProblem *p, long long *volS, long long *cut, long long *volSComp)
{
	int i = 0;

	*volS= 0;
	*cut = 0;
	*volSComp = 0;

	for (i=0; i<(p->numArcs); ++i)
	{
		int from = (p->arcList)[i].from;
		int to = (p->arcList)[i].to;

		if (from == (p->source) && (p->bestSourceSet)[to])
		{
			*cut += (p->arcList)[i].intercept;
			//printf("c add edge[s,%d] to cut with w=%lld\n", origR[to], (p->arcList)[i].intercept);
		}
		else if (to==(p->sink) && (p->bestSourceSet)[from])
		{
			*volS+= (p->arcList)[i].slope;
		}
		else if (to==(p->sink) && !(p->bestSourceSet)[from])
		{
			*volSComp+= (p->arcList)[i].slope;
		}
		else if (from != (p->source) && to != (p->sink) && (p->bestSourceSet)[from] && !(p->bestSourceSet)[to])
		{
			
			*cut += (p->arcList)[i].intercept;
		}

	}

	//printf("c COMP C(S, S_) / q(S) = %lld / %lld  =  %lf\n", *num, *den, (double)(*num)/(*den));
	//*den/=2;


}

static void
computeNumeratorDenominator(CutProblem *p, long long *num, long long *den)
{

	int i = 0;

	*num = 0;
	*den = 0;

	for (i=0; i<(p->numArcs); ++i)
	{
		int from = (p->arcList)[i].from;
		int to = (p->arcList)[i].to;

		if (from == (p->source) && (p->inSourceSet)[to])
		{
			*num += (p->arcList)[i].intercept;
			//printf("c add edge[s,%d] to cut with w=%lld\n", origR[to], (p->arcList)[i].intercept);
		}
		else if (to==(p->sink) && (p->inSourceSet)[from])
		{
			*den += (p->arcList)[i].slope;
		}
		else if (from != (p->source) && to != (p->sink) && (p->inSourceSet)[from] && !(p->inSourceSet)[to])
		{
			
			*num += (p->arcList)[i].intercept;
		}

	}

	//printf("c COMP C(S, S_) / q(S) = %lld / %lld  =  %lf\n", *num, *den, (double)(*num)/(*den));
	//*den/=2;


}


static void
dumpSourceSet (CutProblem *p, FILE *out)
{
  
  char *partition = NULL;
  if ((partition= (char*) malloc ((p->origNumNodes)* sizeof (char))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  
  int i;
  int sourceSetSize = 0;

  for(i=0; i<(p->origNumNodes); ++i)
  {
    (partition)[i] = 0;
  }

  for(i=1; i<(p->numNodes)-1; ++i)
  {
    (partition)[(p->invMapping)[i] -1] = ((p->bestSourceSet)[i]);
  }

  for(i=0; i<(p->origNumNodes); i++)
  {
    fprintf(out, "%d\n", (int) (partition)[i]);
    (p->sourceSetSize) += (partition)[i];
  }
	printf("c best (p->source) set size = %d\n", (p->sourceSetSize));

}

static void
copySourceSet(CutProblem *p)
{
  int i;
  for( i=0; i<(p->numNodes); i++ )
  {
    (p->bestSourceSet)[i] = (p->inSourceSet)[i];
  }
}

static long long 
computeArcCapacity(CutProblem *p, const Arc *ac, long long param)
{
  if( ac->to == (p->sink) )
  {
 
    return lmax( ac->intercept + param*(ac->slope), 0);
  }
  else if( ac->from == (p->source) )
  {
    return lmax( param*(ac->slope) + ac->intercept, 0);
  }
  return ac->intercept;
}

static void
initializeNode (CutProblem *p, Node *nd, const int n)
{
  nd->label = 0;
  nd->excess = 0;
  nd->parent = NULL;
  nd->childList = NULL;
  nd->nextScan = NULL;
  nd->nextArc = 0;
  nd->numOutOfTree = 0;
  nd->arcToParent = NULL;
  nd->next = NULL;
  nd->prev = NULL;
  nd->visited = 0;
  nd->numAdjacent = 0;
  nd->outOfTree = NULL;
  nd->breakpoint = ((p->numParams)+1);
}

static void
initializeRoot (CutProblem *p, Root *rt) 
{
  rt->start = (Node *) malloc (sizeof(Node));
  rt->end = (Node *) malloc (sizeof(Node));

  if ((rt->start == NULL) || (rt->end == NULL))
  {
    printf ("%s Line %d: Out of memory\n", __FILE__, __LINE__);
    exit (1);
  }

  initializeNode (p, rt->start, 0);
  initializeNode (p, rt->end, 0);

  rt->start->next = rt->end;
  rt->end->prev = rt->start;
}


static void
freeRoot (Root *rt) 
{
  free(rt->start);
  rt->start = NULL;

  free(rt->end);
  rt->end = NULL;
}

static void
liftAll (CutProblem *p, Node *rootNode, const long long theparam) 
{
	//printf("c liftAll %d\n", rootNode - (p->adjacencyList));
  Node *temp, *current=rootNode;

  current->nextScan = current->childList;

  -- (p->labelCount)[current->label];
  current->label = (p->numNodes);  
	//printf("c new label of %d is %d\n", current - (p->adjacencyList), current->label);
  current->breakpoint = (theparam+1);


  (p->inSourceSet)[(int)(current-(p->adjacencyList)) ] = 0;
	(p->sourceSetSize)++;
	//printf("remove %d from (p->source) set\n", (int)(current-(p->adjacencyList)) - 1);

  for ( ; (current); current = current->parent)
  {
    while (current->nextScan) 
    {
      temp = current->nextScan;
      current->nextScan = current->nextScan->next;
      current = temp;
      current->nextScan = current->childList;

      (p->inSourceSet)[(int)(current-(p->adjacencyList)) ] = 0;
	    (p->sourceSetSize)++;
			//printf("remove %d from (p->source) set\n", (int)(current-(p->adjacencyList)) - 1);
      -- (p->labelCount)[current->label];
      current->label = (p->numNodes);
			//printf("c new label of %d is %d\n", current - (p->adjacencyList), current->label);
      current->breakpoint = (theparam+1); 
    }
  }
}

static void
addToStrongBucket (Node *newRoot, Node *rootEnd) 
{
  newRoot->next = rootEnd;
  newRoot->prev = rootEnd->prev;
  rootEnd->prev = newRoot;
  newRoot->prev->next = newRoot;
}

static void
createOutOfTree (Node *nd)
{
  if (nd->numAdjacent)
  {
    if ((nd->outOfTree = (Arc **) malloc (nd->numAdjacent * sizeof (Arc *))) == NULL)
    {
      printf ("%s Line %d: Out of memory\n", __FILE__, __LINE__);
      exit (1);
    }
  }
}

static void
initializeArc (Arc *ac)
{
  int i;

  ac->from = 0;
  ac->to = 0;
  ac->capacity = 0;
  ac->flow = 0;
  ac->direction = 1;
  ac->intercept = 0;
  ac->slope = 0;
  //ac->capacities = NULL;
}

static void
addOutOfTreeNode (CutProblem *p, Node *n, Arc *out) 
{
  n->outOfTree[n->numOutOfTree] = out;
  ++ n->numOutOfTree;
}




int cmp_edge(const void *lhs, const void *rhs)
{
  Edge *el = (Edge *)lhs;
  Edge *er = (Edge *)rhs;

  if(el->u < er->u) return -1;
  if(el->u > er->u) return 1;

  if(el->v < er->v) return -1;
  if(el->v > er->v) return 1;

  return 0;
}

int
isDigit(char c)
{
  return c>='0' && c<='9';
}

static char *
tryReadInt( char *ptr, size_t *len, int *in, int *correct )
{
  char c = *ptr;
  *correct = 0;

  while( ! isDigit(c) && (*len) > 0 )
  {
    ptr++;
    c = *ptr;
    (*len)--;
  }

  *in = 0;

  while( isDigit(c) && (*len) > 0)
  {
    *in = (*in * 10 + ( c - '0'));
    *correct = 1;
    ptr++;
    c = *ptr;
    (*len)--;
  }

  return ptr;

}

static int
parseParameterLine(CutProblem *p,  char *line, size_t lineLength, int *n_, int *m_, int *format_)
{
  int format = 0;

  int n = 0;
  int m = 0;
  int correct = 0;
  char *origLine = line;
  line = tryReadInt( line, &lineLength, &n, &correct); 
  
  if(!correct) 
  {
    fprintf(stderr, "Malformed parameter line \'%s\'\n", origLine);
    exit(-1);
  }
  line = tryReadInt( line, &lineLength, &m, &correct); 
  if(!correct) 
  {
    fprintf(stderr, "Malformed parameter line\n");
    exit(-1);
  }
  if( *line == ' ' )
  {
    line = tryReadInt( line, &lineLength, &format, &correct); 
    if (!correct)
    {
      format = 0;
    }
  }

  *n_ = n;
  *m_ = m;
  *format_ = format;

  return 0;
}

static int 
readPartitionFile (CutProblem *p, char *partition, FILE *partitionFile, int n)
{
  int partitionSize = 0;

  int active = 0;
  int i = 0;

  for ( i=1; i<=n; ++i )
  {
    fscanf( partitionFile, "%d", &active);
    active = (active != (p->seedSet));
    partition[i] = active;
    if (active) 
    {
      partitionSize++;
    }
  }

  return partitionSize;
}

static void
computeMappingsFromPartition(CutProblem *p, char *partition, int partitionSize, int n, int **mapping, int **invMapping)
{
  int i = 0;
  int idx = 1;
  if ((*mapping = (int*) malloc ((n+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((*invMapping = (int*) malloc ((partitionSize+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  for (i=1; i<=n; ++i)
  {
    if (partition[i]){
      (*mapping)[i] = idx;
      (*invMapping)[idx] = i;
      idx++;
    }
    else{
      // Collapse node into (p->source) ((p->sink) in paper)
      (*mapping)[i] = 0;
    }
  }
}

static void
parseAdjacencyListLine(CutProblem *p, char *line, size_t lineLength, int nodeIdx, int *eIdx, int *connectedToSink, int *interEdges,  int edgeWeighted, int nodeWeighted, int *edgeWeights, int *nodeWeights, int *from, int *to, char *partition)
{
  int nodeWeight = 0;
  int edgeWeight = 0;
  int fromEdge = nodeIdx;
  int toEdge = 0;

  int correct = 0;

  char *origLine = line;
  *connectedToSink = 0;
  *interEdges = 0;

  int totalWeightsOfNode = 0;
  if (nodeWeighted)
  {
    line = tryReadInt( line, &lineLength, &nodeWeight, &correct);
    if(!correct) 
    {
      fprintf(stderr, "Malformed adjacency list line \'%s\'\n", origLine);
      fprintf(stderr, "Reason: no node weight provided\n");
      exit(-1);
    }
  }
  else
  {
    nodeWeight = 1;
  }

  nodeWeights[nodeIdx] = nodeWeight;
  while (lineLength > 1)
  {
    line = tryReadInt( line, &lineLength, &toEdge, &correct);
    
    from[*eIdx]= fromEdge;
    to[*eIdx]= toEdge;

    if (edgeWeighted)
    {
      line = tryReadInt( line, &lineLength, &edgeWeight, &correct);
      if(!correct) 
      {
        fprintf(stderr, "Malformed adjacency list line \'%s\'\n", origLine);
        fprintf(stderr, "Reason: missing edgeWeight\n");
        exit(-1);
      }
    }
    else
    {
      edgeWeight = 1;
    }
    
    if (partition[fromEdge] && partition[toEdge])
    {
      (*interEdges)++;

    }
    else if (partition[fromEdge] && !partition[toEdge])
    {
      (*connectedToSink) = 1;
    }

    edgeWeights[*eIdx] = edgeWeight;
    totalWeightsOfNode += edgeWeight;
    (*eIdx)++;
  }

}

static void
constructParametricGraph (CutProblem *p, int *from, int *to, int *nodeWeights, int *edgeWeights, char *partition, int *mapping, 
    int n, int m, int totalInterEdges, int numConnectedToSink, int partitionSize)
{

  int i = 0;
  int fromArc = 0;
  int toArc = 0;
  int nodeWeight = 0;
  int edgeWeight = 0;
  int *degToSink = 0;
  int currEdge = 0;
  int currArc = 0;
  Arc *ac = NULL;

  (p->origNumNodes) = (p->n);
  (p->numNodes) = partitionSize + 2;
  (p->numArcs) = partitionSize + totalInterEdges + numConnectedToSink;

  if (((p->adjacencyList) = (Node *) malloc ((p->numNodes) * sizeof (Node))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((degToSink= (int*) malloc ((p->numNodes) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((p->strongRoots = (Root *) malloc ((p->numNodes) * sizeof (Root))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->labelCount) = (int *) malloc ((p->numNodes) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->arcList) = (Arc *) malloc ((p->numArcs) * sizeof (Arc))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->inSourceSet)= (char *) malloc ((p->numNodes) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->bestSourceSet)= (char *) malloc ((p->numNodes) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  for (i=0; i<(p->numNodes); ++i)
  {
    initializeRoot (p, &p->strongRoots[i]);
    initializeNode (p, &(p->adjacencyList)[i], i);
    (p->labelCount)[i] = 0;
    degToSink[i] = 0;
    (p->inSourceSet)[i] = 1;
    (p->bestSourceSet)[i] = 0;
  }

  for (i=0; i<(p->numArcs); ++i)
  {
    initializeArc (&(p->arcList)[i]);
  }

  (p->source) = 0;
  (p->sink) = partitionSize + 1;

  int debugInternalArcs = 0;
  int debugSinkArcs= 0;
  int debugSourceArcs= 0;

  for ( i=0; i<2*m; ++i)
  {
    fromArc = (mapping)[from[i]];
    toArc = (mapping)[to[i]];
    edgeWeight = (edgeWeights)[i];
    
    if (fromArc != (p->source) && toArc != (p->source))
    {
      ac = &(p->arcList)[currArc++];
      ac->from = fromArc;
      ac->to = toArc;
      ac->intercept = edgeWeight*(p->APP_VAL);
      ac->slope = 0;

      ac->capacity = edgeWeight*(p->APP_VAL);

      debugInternalArcs++;
      //++ adjacents[ac->from];
      //++ adjacents[ac->to];
      (p->adjacencyList)[fromArc].numAdjacent++;
      (p->adjacencyList)[toArc].numAdjacent++;
    }
    // We actually dont need toArc == (p->source), but lets keep it for clarity
    else if ( fromArc != (p->source) && toArc == (p->source) )
    {
      degToSink[fromArc] += edgeWeight;
    }

  }

  
  int debugTotNodeWeight = 0;
  for ( i=1; i<=(p->n); ++i)
  {
    fromArc = (mapping)[i];
    nodeWeight = (nodeWeights)[i];
    debugTotNodeWeight += (partition)[i] * (nodeWeights)[i];
    if(fromArc == (p->source))
    {
      (p->initialVolumeComplement) += nodeWeight;
      continue;
    }
    toArc = (p->sink);

    // arc from node to (p->source) ((p->sink) here) with capacity lambda * q_i
    ac = &(p->arcList)[currArc++];
    ac->from = fromArc;
    ac->to = toArc;

    ac->intercept = 0;
    ac->slope = nodeWeight;
    (p->adjacencyList)[fromArc].numAdjacent++;
    (p->adjacencyList)[toArc].numAdjacent++;

    // if its connected to (p->sink) ((p->source) here), add arc with capacity sum_{j \notin V_0} w_ij 

    toArc = fromArc;
    fromArc = (p->source);

    if (degToSink[toArc] == 0) continue;

    ac = &(p->arcList)[currArc++];
    ac->from = fromArc;
    ac->to = toArc;

    ac->intercept = degToSink[toArc]*(p->APP_VAL);
    ac->slope = 0;
    ac->capacity = ac->intercept;
    (p->adjacencyList)[fromArc].numAdjacent++;
    (p->adjacencyList)[toArc].numAdjacent++;
  }

  //printf("c total node weight of (p->partition) = %d\n", debugTotNodeWeight);
	long long numerator = 0;
	long long denominator = 0;

	computeNumeratorDenominator(p, &numerator, &denominator);
	// printf("c C(S,S-)=%lld, d(S)=%lld\n", numerator, denominator);

	(p->currLambda) = numerator/ denominator;
	if ((p->isLambdaInjected))
	{
  	(p->currLambda) = (long long) ((p->injectedLambda)*(p->APP_VAL));
	}
   
  printf("c Initial cut: %lld\n", numerator/(p->APP_VAL));
  printf("c Initial weight = %lld\n", denominator);
  printf("c Initial conductance* = %lf\n", (double)(p->currLambda)/(p->APP_VAL));

  for(i=0; i<(p->numArcs); ++i)
  {
      ac = &(p->arcList)[i];
      ac->capacity = computeArcCapacity(p, ac, (p->currLambda));
			//printf("c arc [%lld,%lld] intercept=%lld slope=%lld arc capacity = %lld\n",
			//		ac->from, ac->to, ac->intercept, ac->slope, ac->capacity);
  }
      
      
  for (i=0; i<(p->numNodes); ++i) 
  {
    createOutOfTree (&(p->adjacencyList)[i]);
  }

  for (i=0; i<(p->numArcs); i++) 
  {
    int to = (p->arcList)[i].to;
    int from = (p->arcList)[i].from;
    long long capacity = (p->arcList)[i].capacity;

    if (!(((p->source) == to) || ((p->sink) == from) || (from == to))) 
    {
      if (((p->source) == from) && (to == (p->sink))) 
      {
        (p->arcList)[i].flow = capacity;
      }
      else if (from == (p->source))
      {
        addOutOfTreeNode (p, &(p->adjacencyList)[from], &(p->arcList)[i]);
      }
      else if (to == (p->sink))
      {
        addOutOfTreeNode (p, &(p->adjacencyList)[to], &(p->arcList)[i]);
      }
      else
      {
        addOutOfTreeNode (p, &(p->adjacencyList)[from], &(p->arcList)[i]);
      }
    }
  }
  
  if (degToSink != NULL)
  {
    free(degToSink);
  }

}

static void
readMetisFormatGraph (CutProblem *p, FILE *stream, FILE *partitionStream)
{
  double startTime = timer();

  char *line = NULL;
  int *mapping = NULL;


  int *edgeWeights = NULL;
  int *nodeWeights = NULL;
  int *from= NULL;
  int *to= NULL;
  
  size_t lineSize = 0;
  size_t lineLength = 0;


  int i=0;
  int n = 0;
  int m = 0;
  int format = 0;
  int partitionSize = 0;
  int numConnectedToSink = 0;
  int totalInterEdges = 0;
  int interEdges = 0;
  int connectedToSink = 0;

  int eIdx = 0;

  int edgeWeighted = 0;
  int nodeWeighted= 0;


  //Start time measure of reading here

  lineLength = getLine(&line, &lineSize, stream);

  while ( line[0] == '%' )
  {
    lineLength = getLine(&line, &lineSize, stream);
  }

  // Parse parameter line
  parseParameterLine(p, line, lineLength, &n, &m, &format);


  if ((from = (int*) malloc ((2*m) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((to = (int*) malloc ((2*m) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }
  edgeWeighted = format%10;
  nodeWeighted = (format/10)%10;

  char *partition = NULL;
  
  if ((partition = (char*) malloc ((n+1) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }
  
  for (i=0; i<=n; i++)
  {
    partition[i] = 0;
  }

  partitionSize = readPartitionFile(p, partition, partitionStream, n);
  computeMappingsFromPartition(p, partition, partitionSize, n, &mapping, &(p->invMapping));

  if ((edgeWeights = (int*) malloc ((2*m) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((nodeWeights = (int*) malloc ((n+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  for (i=1; i<=(p->n); ++i)
  {

    lineLength = getLine(&line, &lineSize, stream);

    while ( line[0] == '%' )
    {
      lineLength = getLine(&line, &lineSize, stream);
    }

    parseAdjacencyListLine(p, line, lineLength, i, &eIdx, &connectedToSink, &interEdges,
        edgeWeighted, nodeWeighted, edgeWeights, nodeWeights, from, to, partition);

    totalInterEdges += interEdges;
    if (connectedToSink) numConnectedToSink++;
  }
  
  (p->readTime) = timer() - startTime;
  // End time measure of read here


  // Start time measure of initialization of flow graph here
  startTime= timer();
  constructParametricGraph(p, from, to, nodeWeights, edgeWeights, partition, mapping, n, m, totalInterEdges, numConnectedToSink, partitionSize);
  (p->initTime) = timer() - startTime; 
  // End time measure of initialization here
  

  free(partition);
  free(line);
  free(edgeWeights);
  free(nodeWeights);
  free(from);
  free(to);
  free(mapping);


}


static void
readGraphFile (CutProblem *p)
{
  double thetime = timer();
  int i;

  (p->n) = 0;
  (p->m) = 0;

	int node = 0;
	int rsize = 0;
	int interEdges = 0;
	int connectedToSink = 0;

  (p->currLambda) = 0;

  (p->n) = readLL();
  (p->m) = readLL();
	rsize = readInt();
	interEdges = readInt();
	connectedToSink = readInt();

	int *mapping = NULL;
	

	
//static int *orEdges = NULL;
//static int *(p->invMapping) = NULL;
//static char *inOrigS = NULL;

  if ((mapping= (int*) malloc (((p->n)+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->invMapping)= (int*) malloc (((p->n)+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }


  if ((p->origDeg= (int*) malloc (((p->n)+1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((p->inOrigS= (char*) malloc (((p->n)+1) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

	for (i=0; i<=(p->n); i++)
	{
		p->inOrigS[i] = 0;
		(p->invMapping)[i] = 0;
		p->origDeg[i] = 0;
	}

  if ((p->orEdges = (int*) malloc (((p->m)<<1) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

	for( i=1; i<=(p->n); i++)
	{
		// assume collapsed into (p->sink) node
		(mapping)[i] = 0;
	}

	for( i=0; i<rsize; i++)
	{
		// node is in R, remove from collapsed and give new ID
		node = readInt();
		(mapping)[node] = i+2;
		(p->invMapping)[i+2] = node;
		p->inOrigS[node] = 1;

	}



  printf("c n=%d m=%d\n", (p->n), (p->m));
  printf("c rsize=%d interEdges=%d connectedToSink=%d\n", rsize, interEdges, connectedToSink);
  (p->source) = 0;
  (p->sink) = 1;

  (p->numNodes) = rsize + 2;
  (p->numArcs) = rsize + 2*interEdges + connectedToSink;

	printf("c (p->numNodes) = %d (p->numArcs) = %d\n", (p->numNodes), (p->numArcs));
  p->adjacents = NULL;

	int *degToSink = NULL;

	//edges that point to something in (p->sink) set
	int collapsedEdges = 0;

  if ((degToSink = (int*) malloc ((rsize) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((p->weights= (int*) malloc ((p->n) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((p->degrees= (int *) malloc ((rsize) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->inSourceSet)= (char *) malloc ((p->n) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->bestSourceSet)= (char *) malloc ((p->n) * sizeof (char))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->adjacencyList) = (Node *) malloc ((p->numNodes) * sizeof (Node))) == NULL)
  {
    printf ("%s, %d: could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if ((p->strongRoots = (Root *) malloc ((p->numNodes) * sizeof (Root))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->labelCount) = (int *) malloc ((p->numNodes) * sizeof (int))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }

  if (((p->arcList) = (Arc *) malloc ((p->numArcs) * sizeof (Arc))) == NULL)
  {
    printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
    exit (1);
  }


  for (i=0; i<rsize; ++i)
  {

    (p->inSourceSet)[i] = 1;

    p->degrees[i] = 0;

		degToSink[i] = 0;
  }

  // Initialize lambda as 


  for (i=0; i<(p->numNodes); ++i)
  {
    initializeRoot (p, &p->strongRoots[i]);
    initializeNode (p, &(p->adjacencyList)[i], i);
    //adjacents[i] = 0;
    (p->labelCount)[i] = 0;
  }

  for (i=0; i<(p->numArcs); ++i)
  {
    initializeArc (&(p->arcList)[i]);
  }

  int currEdge = 0;
  int currArc = 0;
  Arc *ac = NULL;
  // add arc for each edge
	//
	//
	


	// first interEdges arcs for internal edges
	// then connectedToSink arcs for (p->sink) adjacent
	// then rsize arcs for (p->source) adjacent
  for (i=0; i<(p->m); i++)
  {
      int u = 0;
      int v = 0;
      long long w = 1;
      u = readInt();
      v = readInt();
      if ((p->weightedEdges))
      {
        w = readInt();
      }
			p->orEdges[2*i] = u;
			p->orEdges[2*i+1] = v;
			p->origDeg[u]++;
			p->origDeg[v]++;
      int from = (mapping)[u];
      int to = (mapping)[v];

			//both are collapsed, ignore
			if( from == (p->source) && to == (p->source) )
			{
				continue;
			}

			// if arc goes from (p->sink) to non (p->sink), invert it
			if ( from == (p->source))
			{
				swap(&from, &to);
			}



			//goes to collapsed
			if (to == (p->source))
			{
				degToSink[from-2] += w;
				collapsedEdges++;
				continue;
			}

			if (from >= 2)
			{
      	p->degrees[from-2] += w;
			}

			if (to >= 2)
			{
        p->degrees[to-2] += w;
			}
      ac = &(p->arcList)[currArc++];
      ac->from = from;
      ac->to = to;
      ac->intercept = w*(p->APP_VAL);
      ac->capacity = w*(p->APP_VAL);

      ++ p->adjacents[ac->from];
      ++ p->adjacents[ac->to];

      ac = &(p->arcList)[currArc++];
      ac->from = to;
      ac->to = from;
      ac->intercept = w*(p->APP_VAL);
      ac->capacity = w*(p->APP_VAL);

      ++ p->adjacents[ac->from];
      ++ p->adjacents[ac->to];
  }

	printf("c collapsed edges = %d\n", collapsedEdges);
	printf("c currArc = %d\n", currArc);
	//if (currArc != inter


	// can probably optimize this for with only rsize iterations
	for (i=1; i<=(p->n); i++)
	{
		if ((mapping)[i]==0)
		{
			continue;
		}

      int to = (p->sink);
      int from = (mapping)[i]; 

			long long w =  p->degrees[from-2] + degToSink[from-2];
      ac = &(p->arcList)[currArc++];

      ac->from = from;
      ac->to = to;
      ac->intercept = 0;
      ac->slope= w;
      ++ p->adjacents[ac->from];
      ++ p->adjacents[ac->to];

	}

	printf("c currArc = %d\n", currArc);
	// can probably optimize this for with only rsize iterations
	for (i=1; i<=(p->n); i++)
	{
		if ((p->mapping)[i]==0)
		{
			continue;
		}

      int to = (p->mapping)[i]; 
      int from = (p->source);

			long long w = degToSink[to-2];
			if ( w==0 )
			{
				continue;
			}
      ac = &(p->arcList)[currArc++];

      ac->from = from;
      ac->to = to;
      ac->intercept = w*(p->APP_VAL);
      ac->slope = 0;

      ++ adjacents[ac->from];
      ++ adjacents[ac->to];

	}

	printf("c currArc = %d\n", currArc);
	printf("c (p->numArcs) = %d\n", (p->numArcs));

  for(i=0; i<(p->numNodes); ++i)
  {
    (p->adjacencyList)[i].numAdjacent = adjacents[i];
  }

	long long numerator = 0;
	long long denominator = 0;

	computeNumeratorDenominator(&numerator, &denominator);
	// printf("c C(S,S-)=%lld, d(S)=%lld\n", numerator, denominator);

	(p->currLambda) = numerator/ denominator;
	if ((p->isLambdaInjected))
	{
  	(p->currLambda) = (long long) ((p->injectedLambda)*(p->APP_VAL));
	}
   
  printf("c Initial lambda = %lf\n", (double)(p->currLambda)/(p->APP_VAL));

  for(i=0; i<(p->numArcs); ++i)
  {
      ac = &(p->arcList)[i];
      ac->capacity = computeArcCapacity(ac, (p->currLambda));
			//printf("c arc [%lld,%lld] intercept=%lld slope=%lld arc capacity = %lld\n",
			//		ac->from, ac->to, ac->intercept, ac->slope, ac->capacity);
  }
      
      
  for (i=0; i<(p->numNodes); ++i) 
  {
    createOutOfTree (&(p->adjacencyList)[i]);
  }

  for (i=0; i<(p->numArcs); i++) 
  {
    int to = (p->arcList)[i].to;
    int from = (p->arcList)[i].from;
    long long capacity = (p->arcList)[i].capacity;

    if (!(((p->source) == to) || ((p->sink) == from) || (from == to))) 
    {
      if (((p->source) == from) && (to == (p->sink))) 
      {
        (p->arcList)[i].flow = capacity;
      }
      else if (from == (p->source))
      {
        addOutOfTreeNode (&(p->adjacencyList)[from], &(p->arcList)[i]);
      }
      else if (to == (p->sink))
      {
        addOutOfTreeNode (&(p->adjacencyList)[to], &(p->arcList)[i]);
      }
      else
      {
        addOutOfTreeNode (&(p->adjacencyList)[from], &(p->arcList)[i]);
      }
    }
  }




  free(adjacents);
	free((p->mapping));
  adjacents = NULL;



  (p->initTime) = timer()-thetime;
}


static void
simpleInitialization (CutProblem *p, void) 
{
  int i, size;
  Arc *tempArc;

  size = (p->adjacencyList)[(p->source)].numOutOfTree;
  for (i=0; i<size; ++i) 
  {
    tempArc = (p->adjacencyList)[(p->source)].outOfTree[i];
    tempArc->flow = tempArc->capacity;
    (p->adjacencyList)[tempArc->to].excess += tempArc->capacity;
  }

  size = (p->adjacencyList)[(p->sink)].numOutOfTree;
  for (i=0; i<size; ++i)
  {
    tempArc = (p->adjacencyList)[(p->sink)].outOfTree[i];
    tempArc->flow = tempArc->capacity;
    (p->adjacencyList)[tempArc->from].excess -= tempArc->capacity;
  }

  (p->adjacencyList)[(p->source)].excess = 0;
  (p->adjacencyList)[(p->sink)].excess = 0;

  for (i=0; i<(p->numNodes); ++i) 
  {
    if ((p->adjacencyList)[i].excess > 0) 
    {
        (p->adjacencyList)[i].label = 1;
      ++ (p->labelCount)[1];

      addToStrongBucket (&(p->adjacencyList)[i], strongRoots[1].end);
    }
  }

  (p->adjacencyList)[(p->source)].label = (p->numNodes);
  (p->adjacencyList)[(p->source)].breakpoint = 0;
  (p->adjacencyList)[(p->sink)].label = 0;
  (p->adjacencyList)[(p->sink)].breakpoint = ((p->numParams)+2);
  (p->labelCount)[0] = ((p->numNodes) - 2) - (p->labelCount)[1];
}

static inline int 
addRelationship (CutProblem *p, Node *newParent, Node *child) 
{
	//printf("c add relationship parent=%d child=%d\n", newParent - (p->adjacencyList), child-(p->adjacencyList));
  child->parent = newParent;
  child->next = newParent->childList;
	
//mi cambio

	if (newParent->childList != NULL)
	{
		newParent->childList->prev = child;
	}

//end mi cambio

  newParent->childList = child;

  return 0;
}

static inline void
breakRelationship (CutProblem *p, Node *oldParent, Node *child) 
{
	//printf("c break relationship parent=%d child=%d\n", oldParent - (p->adjacencyList), child-(p->adjacencyList));
  Node *current;

  child->parent = NULL;

  if (oldParent->childList == child) 
  {
    oldParent->childList = child->next;
    child->next = NULL;
    return;
  }

  //for (current = oldParent->childList; (current->next != child); current = current->next);
	current = child->prev;

  current->next = child->next;
	if(child->next != NULL) child->next->prev = current;
  child->next = NULL;
}

static void
merge (CutProblem *p, Node *parent, Node *child, Arc *newArc) 
{
  Arc *oldArc;
  Node *current = child, *oldParent, *newParent = parent;

#ifdef STATS
  ++ (p->numMergers);
#endif

  while (current->parent) 
  {
    oldArc = current->arcToParent;
    current->arcToParent = newArc;
    oldParent = current->parent;
    breakRelationship (oldParent, current);
    addRelationship (newParent, current);
    newParent = current;
    current = oldParent;
    newArc = oldArc;
    newArc->direction = 1 - newArc->direction;
  }

  current->arcToParent = newArc;
  addRelationship (newParent, current);
}


static inline void 
pushUpward (Arc *currentArc, Node *child, Node *parent, const long long resCap) 
{
#ifdef STATS
  ++ (p->numPushes);
#endif

  if (resCap >= child->excess) 
  {
    parent->excess += child->excess;
    currentArc->flow += child->excess;
    child->excess = 0;
    return;
  }

  currentArc->direction = 0;
  parent->excess += resCap;
  child->excess -= resCap;
  currentArc->flow = currentArc->capacity;
  parent->outOfTree[parent->numOutOfTree] = currentArc;
  ++ parent->numOutOfTree;
  breakRelationship (parent, child);

#ifdef LOWEST_LABEL
	(p->lowestStrongLabel) = child->label;
#endif


  addToStrongBucket (child, strongRoots[child->label].end);
}


static inline void
pushDownward (CutProblem *p, Arc *currentArc, Node *child, Node *parent, long long flow) 
{
#ifdef STATS
  ++ (p->numPushes);
#endif

  if (flow >= child->excess) 
  {
    parent->excess += child->excess;
    currentArc->flow -= child->excess;
    child->excess = 0;
    return;
  }

  currentArc->direction = 1;
  child->excess -= flow;
  parent->excess += flow;
  currentArc->flow = 0;
  parent->outOfTree[parent->numOutOfTree] = currentArc;
  ++ parent->numOutOfTree;
  breakRelationship (parent, child);

#ifdef LOWEST_LABEL
	(p->lowestStrongLabel) = child->label;
#endif

  addToStrongBucket (child, strongRoots[child->label].end);
}

static void
pushExcess (CutProblem *p, Node *strongRoot) 
{
  Node *current, *parent;
  Arc *arcToParent;

  for (current = strongRoot; (current->excess && current->parent); current = parent) 
  {
    parent = current->parent;
    arcToParent = current->arcToParent;
    if (arcToParent->direction)
    {
      pushUpward (arcToParent, current, parent, (arcToParent->capacity - arcToParent->flow)); 
    }
    else
    {
      pushDownward (arcToParent, current, parent, arcToParent->flow); 
    }
  }

  if (current->excess > 0) 
  {
    if (!current->next)
    {
			//maybe this is buggy
#ifdef LOWEST_LABEL
	(p->lowestStrongLabel) = current->label;
#endif
      addToStrongBucket (current, strongRoots[current->label].end);
    }
  }
}


static Arc *
findWeakNode (CutProblem *p, Node *strongNode, Node **weakNode) 
{
  int i, size;
  Arc *out;

  size = strongNode->numOutOfTree;

  for (i=strongNode->nextArc; i<size; ++i) 
  {

#ifdef STATS
    ++ (p->numArcScans);
#endif

#ifdef LOWEST_LABEL
    if ((p->adjacencyList)[strongNode->outOfTree[i]->to].label == ((p->lowestStrongLabel)-1)) 
#else
    if ((p->adjacencyList)[strongNode->outOfTree[i]->to].label == ((p->highestStrongLabel)-1)) 
#endif
    {
      strongNode->nextArc = i;
      out = strongNode->outOfTree[i];
      (*weakNode) = &(p->adjacencyList)[out->to];
      -- strongNode->numOutOfTree;
      strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
      return (out);
    }
#ifdef LOWEST_LABEL
    else if ((p->adjacencyList)[strongNode->outOfTree[i]->from].label == ((p->lowestStrongLabel)-1)) 
#else
    else if ((p->adjacencyList)[strongNode->outOfTree[i]->from].label == ((p->highestStrongLabel)-1)) 
#endif
    {
      strongNode->nextArc = i;
      out = strongNode->outOfTree[i];
      (*weakNode) = &(p->adjacencyList)[out->from];
      -- strongNode->numOutOfTree;
      strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
      return (out);
    }
  }

  strongNode->nextArc = strongNode->numOutOfTree;

  return NULL;
}


static void
checkChildren (CutProblem *p, Node *curNode) 
{
	//printf("c checkChildren node %d with label %d (%d with same label)\n", curNode - (p->adjacencyList), curNode->label, (p->labelCount)[curNode->label]);
	int iters = 0;
	//if( (p->labelCount)[curNode->label] != 1 )
	//{
  	for ( ; (curNode->nextScan); curNode->nextScan = curNode->nextScan->next)
  	{
			iters++;
    	if (curNode->nextScan->label == curNode->label)
    	{
				if(iters>=10000)
				{
					//printf("c too many iters %d\n", iters);
				}
				//printf("c found same at iters = %d sameNode = %d\n", iters, curNode->nextScan - (p->adjacencyList));
      	return;
    	}
    
  	}
	//}
	//else
	//{
		//printf("c no same label, skipped\n");
	//}

	//printf("c relabel iters = %d\n", iters);

  -- (p->labelCount)[curNode->label];
  ++  curNode->label;
  ++ (p->labelCount)[curNode->label];
	//printf("c new label of %d is %d\n", curNode - (p->adjacencyList), curNode->label);
  ++ (p->numRelabels);

  curNode->nextArc = 0;
}

static void
processRoot (CutProblem *p, Node *strongRoot) 
{
	//printf("c processRoot %d\n", strongRoot - (p->adjacencyList));
  Node *temp, *strongNode = strongRoot, *weakNode;
  Arc *out;

  strongRoot->nextScan = strongRoot->childList;

  if ((out = findWeakNode (strongRoot, &weakNode)))
  {
		//printf("c merge weakNode strongNode %d %d\n", weakNode-(p->adjacencyList) , strongNode-(p->adjacencyList));
    merge (weakNode, strongNode, out);
    pushExcess (strongRoot);
    return;
  }

  checkChildren (strongRoot);
  
  while (strongNode)
  {
    while (strongNode->nextScan) 
    {
      temp = strongNode->nextScan;
      strongNode->nextScan = strongNode->nextScan->next;
      strongNode = temp;
      strongNode->nextScan = strongNode->childList;

      if ((out = findWeakNode (strongNode, &weakNode)))
      {
				//printf("c merge weakNode strongNode %d %d\n", weakNode-(p->adjacencyList) , strongNode-(p->adjacencyList));
        merge (weakNode, strongNode, out);
        pushExcess (strongRoot);
        return;
      }

      checkChildren (strongNode);
    }

    if ((strongNode = strongNode->parent))
    {
      checkChildren (strongNode);
    }
  }

  addToStrongBucket (strongRoot, strongRoots[strongRoot->label].end);
	++(p->highestStrongLabel);
}

static Node *
getLowestStrongRoot (CutProblem *p, const long long theparam)
{
	int i;
	Node *strongRoot;

	if ((p->lowestStrongLabel) == 0)
	{
		while(strongRoots[0].start->next != strongRoots[0].end)
		{
			strongRoot = strongRoots[0].start->next;
			strongRoot->next->prev = strongRoot->prev;
			strongRoot->prev->next = strongRoot->next;
			strongRoot->next = NULL;
			strongRoot->label = 1;

			--(p->labelCount)[0];
			++(p->labelCount)[1];

    	addToStrongBucket (strongRoot, strongRoots[strongRoot->label].end);

		}
		(p->lowestStrongLabel) = 1;
	}

	for (i=(p->lowestStrongLabel); i<(p->numNodes); ++i)
	{
		if (strongRoots[i].start->next != strongRoots[i].end)
		{
			(p->lowestStrongLabel) = i;
		
			if ((p->labelCount)[i-1] == 0)
			{
				return NULL;
			}

			strongRoot = strongRoots[i].start->next;
			strongRoot->next->prev = strongRoot->prev;
			strongRoot->prev->next = strongRoot->next;
			strongRoot->next = NULL;
			return strongRoot;
		}
	}

	(p->lowestStrongLabel) = (p->numNodes);
	return NULL;
}

		

static Node *
getHighestStrongRoot (CutProblem *p, const long long theparam) 
{
  int i;
  Node *strongRoot;

  for (i=(p->highestStrongLabel); i>0; --i) 
  {
    if (strongRoots[i].start->next != strongRoots[i].end)  
    {
      (p->highestStrongLabel) = i;
      if ((p->labelCount)[i-1]) 
      {
        strongRoot = strongRoots[i].start->next;
        strongRoot->next->prev = strongRoot->prev;
        strongRoot->prev->next = strongRoot->next;
        strongRoot->next = NULL;
        return strongRoot;        
      }

      while (strongRoots[i].start->next != strongRoots[i].end) 
      {

#ifdef STATS
        ++ (p->numGaps);
#endif
        strongRoot = strongRoots[i].start->next;
        strongRoot->next->prev = strongRoot->prev;
        strongRoot->prev->next = strongRoot->next;
        liftAll (strongRoot, theparam);
      }
    }
  }

  if (strongRoots[0].start->next == strongRoots[0].end) 
  {
    return NULL;
  }

  while (strongRoots[0].start->next != strongRoots[0].end) 
  {
    strongRoot = strongRoots[0].start->next;
    strongRoot->next->prev = strongRoot->prev;
    strongRoot->prev->next = strongRoot->next;

    strongRoot->label = 1;
		
	  //printf("c new label of %d is %d\n", strongRoot- (p->adjacencyList), strongRoot->label);
    -- (p->labelCount)[0];
    ++ (p->labelCount)[1];

    ++ (p->numRelabels);

    addToStrongBucket (strongRoot, strongRoots[strongRoot->label].end);
  } 

  (p->highestStrongLabel) = 1;

  strongRoot = strongRoots[1].start->next;
  strongRoot->next->prev = strongRoot->prev;
  strongRoot->prev->next = strongRoot->next;
  strongRoot->next = NULL;

  return strongRoot;  
}


static void
updateCapacities (CutProblem *p, const long long theparam)
{
  int i, size;
  long long delta;
  Arc *tempArc;
  Node *tempNode;

  long long param =  (p->currLambda) ; ///lambdaStart + ((lambdaEnd-lambdaStart) *  ((double)theparam/((p->numParams)-1)));
  size = (p->adjacencyList)[(p->source)].numOutOfTree;
  for (i=0; i<size; ++i) 
  {
    tempArc = (p->adjacencyList)[(p->source)].outOfTree[i];
    //delta = (tempArc->capacities[theparam] - tempArc->capacity);
    delta = ( computeArcCapacity(tempArc, param) - tempArc->capacity);
    //delta = overestimate(delta);
    if (delta < 0)
    {
      printf ("c Error on (p->source)-adjacent arc (%d, %d): capacity decreases by %f at parameter %d.\n",
        tempArc->from,
        tempArc->to,
        (-delta),
        (theparam+1));
      exit(0);
    }

    tempArc->capacity += delta;
    tempArc->flow += delta;
    (p->adjacencyList)[tempArc->to].excess += delta;
    //tempArc->capacity = overestimate(tempArc->capacity);
    //tempArc->flow = overestimate(tempArc->flow);
    //(p->adjacencyList)[tempArc->to].excess = overestimate((p->adjacencyList)[tempArc->to].excess);

    if (((p->adjacencyList)[tempArc->to].label < (p->numNodes)) && ((p->adjacencyList)[tempArc->to].excess > 0))
    {
      pushExcess (&(p->adjacencyList)[tempArc->to]);
    }
  }

  size = (p->adjacencyList)[(p->sink)].numOutOfTree;
  for (i=0; i<size; ++i)
  {
    tempArc = (p->adjacencyList)[(p->sink)].outOfTree[i];
    //delta = (tempArc->capacities[theparam] - tempArc->capacity);
    delta = (computeArcCapacity(tempArc, param) - tempArc->capacity);
    //delta = overestimate(delta);
    if (delta > 0)
    {
      printf ("c Error on (p->sink)-adjacent arc (%d, %d): capacity %d increases to %d at parameter %d.\n",
        tempArc->from,
        tempArc->to,
        tempArc->capacity,
        tempArc->capacity + delta,
        (theparam+1));
      exit(0);
    }

    tempArc->capacity += delta;
    tempArc->flow += delta;
    (p->adjacencyList)[tempArc->from].excess -= delta;

    //tempArc->capacity = overestimate(tempArc->capacity);
    //tempArc->flow = overestimate(tempArc->flow);
    //(p->adjacencyList)[tempArc->from].excess = overestimate((p->adjacencyList)[tempArc->from].excess);
    if (((p->adjacencyList)[tempArc->from].label < (p->numNodes)) && ((p->adjacencyList)[tempArc->from].excess > 0))
    {
      pushExcess (&(p->adjacencyList)[tempArc->from]);
    }
  }

  (p->highestStrongLabel) = ((p->numNodes)-1);
}

static long long
computeMinCut (CutProblem *p, void)
{
  int i;
  long long mincut = 0;

  for (i=0; i<(p->numArcs); ++i) 
  {
    if (((p->adjacencyList)[(p->arcList)[i].from].label >= (p->numNodes)) && ((p->adjacencyList)[(p->arcList)[i].to].label < (p->numNodes)))
    {
      mincut += (p->arcList)[i].capacity;
    }
  }
  return mincut;
}

#ifdef SIMPLE_PARAMETRIC

static void
pseudoflowPhase1 (CutProblem *p, void) 
{
	Node *strongRoot;
  long long css = 0;
  long long ds = 0;
	int param = 0;

	double thetime=timer();

	//computeNumeratorDenominator( &css, &ds);
	//printf("c B lambda;cut;deg;relabels\n");
	//c B lambda;C(S,\bar{S});d(S) 
	//printf("c B %lf;%lld;%lld;%lf;%lld\n", (double)(p->currLambda)/(p->APP_VAL), css, ds, timer()-thetime, (p->numRelabels) );

	thetime = timer ();
//	while ((strongRoot = getHighestStrongRoot ((p->currLambda))))  

#ifdef LOWEST_LABEL
	while ((strongRoot = getLowestStrongRoot ((p->currLambda))))  
#else
	while ((strongRoot = getHighestStrongRoot ((p->currLambda))))  
#endif
	{ 
		processRoot (strongRoot);
	}
	/*
	flow_type mincut = computeMinCut();
	printf ("c Finished solving parameter %d\nc Flow: %lf\nc Elapsed time: %.3lf\n", 
		(theparam),
		mincut,
		(timer () - thetime));

		*/

  copySourceSet();

	dumpSourceSetFile = fopen( "init_iter.txt", "w");
	dumpSourceSet(dumpSourceSetFile);
	fclose(dumpSourceSetFile);


	    computeNumeratorDenominator( &css, &ds);
      long long val = css - (p->currLambda) * ds;

			printf("c C(S,S_) - lambda * ds = %lld - %lld*%lld = %lld\n", css, (p->currLambda), ds, val);
	for (; (p->currLambda) >= 0; --(p->currLambda))
	{
		//printf("c test for lambda = %lf\n", (double)(p->currLambda)/1000);
		
		//if((p->currLambda)%10000 == 0) printf("."); 
		updateCapacities ((p->currLambda));
		long long oldSourceSetSize = (p->sourceSetSize);
#ifdef PROGRESS
		fflush (stdout);
#endif

#ifdef LOWEST_LABEL
	while ((strongRoot = getLowestStrongRoot ((p->currLambda))))  
#else
	while ((strongRoot = getHighestStrongRoot ((p->currLambda))))  
#endif
		{ 
			processRoot (strongRoot);
		}

		if (oldSourceSetSize != (p->sourceSetSize))
		{
			// breakpoint
	    computeNumeratorDenominator( &css, &ds);
			//c B lambda;C(S,\bar{S});d(S) 
	    printf("c B %lf;%lld;%lld;%lf;%lld\n", (double)(p->currLambda)/(p->APP_VAL), css, ds, timer()-thetime, (p->numRelabels) );
			if (css == 0) break;
		}

	}
}

#endif

static void
computeNextCut(CutProblem *p, long long theparam)
{

  printf("c Computing mincut for lambda = %lf\n", (double)theparam/(p->APP_VAL));
  Node *strongRoot;
#ifdef LOWEST_LABEL
	while ((strongRoot = getLowestStrongRoot (theparam)))  
#else
	while ((strongRoot = getHighestStrongRoot (theparam)))  
#endif
  { 
    processRoot (strongRoot);
  }
}

static void
incrementalCut(CutProblem *p, void) 
{
  Node *strongRoot;

  double thetime;
  long long theparam = (p->currLambda);
  thetime = timer ();

  printf("c ----------------------------------------------------------------------------- \n");
  //(p->currLambda) = overestimate((p->currLambda)); //ceil( (p->currLambda) * (p->APP_VAL) ) / (p->APP_VAL);
  long long initLambda = (p->currLambda);
  long long bestLambda = (p->currLambda);
  long long numerator = 0;
  long long denominator = 0;
  copySourceSet();
	// printf("c B lambda;cut;deg;time;relabels\n");
	//computeNumeratorDenominator( &numerator, &denominator);
	// printf("c B %lf;%lld;%lld;%lf;%lld\n", (double)(p->currLambda)/(p->APP_VAL), numerator, denominator, timer()-thetime, (p->numRelabels) );
  int iteration = 1;
  long long val = 0;

  for (iteration = 1; ; ++iteration)
  {
    printf("c Iteration %d\n", iteration);
    
    computeNextCut(theparam);
    
    computeNumeratorDenominator(&numerator, &denominator);
    
    if ( denominator == 0 )
    {
      printf("c    Infeasible solution found. Stopping\n");
      printf("c ----------------------------------------------------------------------------- \n");
      break;
    }

    val = numerator - (p->currLambda) * denominator;
    (p->currLambda) = numerator/denominator;
    bestLambda = (p->currLambda);
    if ( val == 0 )
    {
      printf("c      Optimal solution Found\n");
    }
    printf("c      Cut value: %lld\n", numerator/(p->APP_VAL));
    printf("c      Weight value: %lld\n", denominator);
    printf("c      conductance* value: %lf\n", (double)(p->currLambda)/(p->APP_VAL) );

    copySourceSet();
    if (val == 0)
    {
      printf("c ----------------------------------------------------------------------------- \n");
      break;
    }
		theparam = (p->currLambda);
    printf("c      Updating capacities for lambda = %lf\n", (double)(p->currLambda)/(p->APP_VAL));
    updateCapacities(theparam);
    printf("c ----------------------------------------------------------------------------- \n");
  }


  printf("o Final conductance* found is %lf\n", (double) bestLambda/(p->APP_VAL));
  long long volS = 0;
  long long volSComp = 0;
  long long cutValue = 0;

  computeValuesLastPartition(&volS, &cutValue, &volSComp);

  volSComp += (p->initialVolumeComplement);
  double finalValue = ( (double)cutValue / fmin(volS, volSComp)) / (p->APP_VAL) ;

  printf("c \\frac{C(S,\\bar{S})}{ min(q(S), q(\\bar{S}) ) } = \\frac{%lld}{ min(%lld, %lld ) } = %lf\n",
      cutValue/(p->APP_VAL), volS, volSComp, finalValue );


  //printf("c Computing mincut for lambda = %lf\n", (double)(p->currLambda)/(p->APP_VAL));
  //while ((strongRoot = getHighestStrongRoot (theparam)))  

  //computeNextCut(theparam);

	// long long mincut = computeMinCut();
	// printf("c Initial mincut is = %lld\n", mincut);

	//computeNumeratorDenominator( &numerator, &denominator);
	//printf("c B %lf;%lld;%lld\n", (double)(p->currLambda)/(p->APP_VAL), numerator, denominator );
  //(p->currLambda) = css / qs;

  // printf("c C(S,S-)/d(S) = %lld/%lld = %lld\n", numerator, denominator, ceil_div(numerator, denominator));
  //long long val = numerator - (p->currLambda) * denominator;

  // printf("C(S,S-) - lambda * d(S) = %lld\n", val);
	//int better = 1;

  /*
  while ( denominator != 0 && better)
  {
    // compute new lambda
		better = 0;
    //printf("c Iteration %d\n", iteration++);
    printf("c      Cut value: %lld\n", numerator/(p->APP_VAL));
    printf("c      Weight value: %lld\n", denominator);
    printf("c      conductance* value: %lf\n", (double)numerator/denominator/(p->APP_VAL) );
    (p->currLambda) = numerator / denominator ;//ceil_div(numerator, denominator);
    if (denominator == 0 ) break;
		theparam = (p->currLambda);
    if ((p->currLambda) <  bestLambda)
    {
			better = 1;
      bestLambda = (p->currLambda);
      copySourceSet();
    }

    printf("c updating capacities for lambda = %lf\n", (double)currlambda/app_val);
    updatecapacities(theparam);

#ifdef LOWEST_LABEL
	while ((strongRoot = getLowestStrongRoot (theparam)))  
#else
	while ((strongRoot = getHighestStrongRoot (theparam)))  
#endif
    { 
      processRoot (strongRoot);
    }
	  computeNumeratorDenominator( &numerator, &denominator);
    //mincut = computeMinCut();

		if( denominator != 0 )
		{
	    //printf("c B %lf;%lld;%lld;%lf;%lld\n", (double)(p->currLambda)/(p->APP_VAL), numerator, denominator, timer()-thetime, (p->numRelabels) );
  		//printf("c C(S,S-)/d(S) = %lld/%lld = %lld\n", numerator, denominator, numerator/denominator);
		}
		else
		{
			break;
		}
		val = numerator - (p->currLambda) * denominator;
    
  	//printf("C(S,S-) - lambda * d(S) = %lld\n", val);
  }



	computeNumeratorDenominator( &numerator, &denominator);
  if ( denominator !=0 )
  {
    (p->currLambda) = numerator/denominator;
    bestLambda = fmax((p->currLambda), bestLambda);
  }
  double totalTime = timer()-thetime;

  */
  //printf("c %d,%d,%.4lf,%.4lf,%.4lf,%.4lf,%d\n", (p->n), (p->m), (p->initTime), totalTime, (double)initLambda/(p->APP_VAL), (double)bestLambda/(p->APP_VAL),iteration);
  //printf("o Final conductance* found is %lf\n", (double) bestLambda/(p->APP_VAL));
  //printf("s Time to initialize was %lf\n", (p->initTime));
  //printf("s Total time was %lf\n", totalTime);
  if ( dumpSourceSetFile != NULL )
	{
    printf("c Dumping (p->source) set to file\n");
		dumpSourceSet(dumpSourceSetFile);
		fclose(dumpSourceSetFile);
  }	
  else
  {
    printf("c To dump (p->source) set into file, please use option --dumpSourceSet filename\n");
  }

}

static void
checkOptimality (CutProblem *p, void) 
{
  int i, check = 1;
  long long mincut = 0, *excess; 

  excess = (long long *) malloc ((p->numNodes) * sizeof (long long));
  if (!excess)
  {
    printf ("%s Line %d: Out of memory\n", __FILE__, __LINE__);
    exit (1);
  }

  for (i=0; i<(p->numNodes); ++i)
  {
    excess[i] = 0;
  }

  for (i=0; i<(p->numArcs); ++i) 
  {
    if (((p->adjacencyList)[(p->arcList)[i].from].label >= (p->numNodes)) && ((p->adjacencyList)[(p->arcList)[i].to].label < (p->numNodes)))
    {
      mincut += (p->arcList)[i].capacity;
    }

    if (((p->arcList)[i].flow > (p->arcList)[i].capacity) || ((p->arcList)[i].flow < 0)) 
    {
      check = 0;
      printf("c Capacity constraint violated on arc (%d, %d)\n", 
        (p->arcList)[i].from,
        (p->arcList)[i].to);
    }
    excess[(p->arcList)[i].from ] -= (p->arcList)[i].flow;
    excess[(p->arcList)[i].to ] += (p->arcList)[i].flow;
  }

  for (i=0; i<(p->numNodes); i++) 
  {
    if ((i != ((p->source))) && (i != ((p->sink)))) 
    {
      if (excess[i]) 
      {
        check = 0;
        printf ("c Flow balance constraint violated in node %d. Excess = %lld\n", 
          i+1,
          excess[i]);
      }
    }
  }

  if (check)
  {
    printf ("c\nc Solution checks as feasible.\n");
  }

  check = 1;

  if (excess[(p->sink)] != mincut) 
  {
    check = 0;
    printf("c Flow is not optimal - max flow does not equal min cut!\nc\n");
  }

  if (check) 
  {
    printf ("c\nc Solution checks as optimal.\nc \n");
    printf ("s Max Flow            : %lf\n", mincut);
  }

  free (excess);
  excess = NULL;
}


static void
quickSort (CutProblem *p, Arc **arr, const int first, const int last)
{
  int i, j, left=first, right=last, mid, pivot;
	long long x1, x2, x3, pivotval;
  Arc *swap;

  if ((right-left) <= 5)
  {// Bubble sort if 5 elements or less
    for (i=right; (i>left); --i)
    {
      swap = NULL;
      for (j=left; j<i; ++j)
      {
        if (arr[j]->flow < arr[j+1]->flow)
        {
          swap = arr[j];
          arr[j] = arr[j+1];
          arr[j+1] = swap;
        }
      }

      if (!swap)
      {
        return;
      }
    }

    return;
  }

  mid = (first+last)/2;

  x1 = arr[first]->flow; 
  x2 = arr[mid]->flow; 
  x3 = arr[last]->flow;

  pivot = mid;
  
  if (x1 <= x2)
  {
    if (x2 > x3)
    {
      pivot = left;

      if (x1 <= x3)
      {
        pivot = right;
      }
    }
  }
  else
  {
    if (x2 <= x3)
    {
      pivot = right;

      if (x1 <= x3)
      {
        pivot = left;
      }
    }
  }

  pivotval = arr[pivot]->flow;

  swap = arr[first];
  arr[first] = arr[pivot];
  arr[pivot] = swap;

  left = (first+1);

  while (left < right)
  {
    if (arr[left]->flow < pivotval)
    {
      swap = arr[left];
      arr[left] = arr[right];
      arr[right] = swap;
      -- right;
    }
    else
    {
      ++ left;
    }
  }

  swap = arr[first];
  arr[first] = arr[left];
  arr[left] = swap;

  if (first < (left-1))
  {
    quickSort (arr, first, (left-1));
  }
  
  if ((left+1) < last)
  {
    quickSort (arr, (left+1), last);
  }
}

static void
sort (Node * current)
{
  if (current->numOutOfTree > 1)
  {
    quickSort (current->outOfTree, 0, (current->numOutOfTree-1));
  }
}

static void
minisort (CutProblem *p, Node *current) 
{
  Arc *temp = current->outOfTree[current->nextArc];
  int i, size = current->numOutOfTree;
	long long tempflow = temp->flow;

  for(i=current->nextArc+1; ((i<size) && (tempflow < current->outOfTree[i]->flow)); ++i)
  {
    current->outOfTree[i-1] = current->outOfTree[i];
  }
  current->outOfTree[i-1] = temp;
}

static void
decompose (CutProblem *p, Node *excessNode, const int (p->source), int *iteration) 
{
  Node *current = excessNode;
  Arc *tempArc;
  long long bottleneck = excessNode->excess;

  for ( ;(((int)(current-(p->adjacencyList))) != (p->source)) && (current->visited < (*iteration)); 
        current = &(p->adjacencyList)[tempArc->from])
  {
    current->visited = (*iteration);
    tempArc = current->outOfTree[current->nextArc];

    if (tempArc->flow < bottleneck)
    {
      bottleneck = tempArc->flow;
    }
  }

  if ((int)((int)(current-(p->adjacencyList))) == (p->source)) 
  {
    excessNode->excess -= bottleneck;
    current = excessNode;

    while ((int)((int)(current-(p->adjacencyList))) != (p->source)) 
    {
      tempArc = current->outOfTree[current->nextArc];
      tempArc->flow -= bottleneck;

      if (tempArc->flow) 
      {
        minisort(current);
      }
      else 
      {
        ++ current->nextArc;
      }
      current = &(p->adjacencyList)[tempArc->from];
    }
    return;
  }

  ++ (*iteration);

  bottleneck = current->outOfTree[current->nextArc]->flow;

  while (current->visited < (*iteration))
  {
    current->visited = (*iteration);
    tempArc = current->outOfTree[current->nextArc];

    if (tempArc->flow < bottleneck)
    {
      bottleneck = tempArc->flow;
    }
    current = &(p->adjacencyList)[tempArc->from];
  } 
  
  ++ (*iteration);

  while (current->visited < (*iteration))
  {
    current->visited = (*iteration);

    tempArc = current->outOfTree[current->nextArc];
    tempArc->flow -= bottleneck;

    if (tempArc->flow) 
    {
      minisort(current);
      current = &(p->adjacencyList)[tempArc->from];
    }
    else 
    {
      ++ current->nextArc;
      current = &(p->adjacencyList)[tempArc->from];
    }
  }
}

static void
recoverFlow (CutProblem *p, void)
{
  int i, j, iteration = 1;
  Arc *tempArc;
  Node *tempNode;

  for (i=0; i<(p->adjacencyList)[(p->sink)].numOutOfTree; ++i) 
  {
    tempArc = (p->adjacencyList)[(p->sink)].outOfTree[i];
    if ((p->adjacencyList)[tempArc->from].excess < 0) 
    {
      tempArc->flow -= (long long) (-1 * (p->adjacencyList)[tempArc->from].excess); 
      (p->adjacencyList)[tempArc->from].excess = 0;
    } 
  }

  for (i=0; i<(p->adjacencyList)[(p->source)].numOutOfTree; ++i) 
  {
    tempArc = (p->adjacencyList)[(p->source)].outOfTree[i];
    addOutOfTreeNode (&(p->adjacencyList)[tempArc->to], tempArc);
  }

  (p->adjacencyList)[(p->source)].excess = 0;
  (p->adjacencyList)[(p->sink)].excess = 0;

  for (i=0; i<(p->numNodes); ++i) 
  {
    tempNode = &(p->adjacencyList)[i];

    if ((i == ((p->source))) || (i == ((p->sink))))
    {
      continue;
    }

    if (tempNode->label >= (p->numNodes)) 
    {
      tempNode->nextArc = 0;
      if ((tempNode->parent) && (tempNode->arcToParent->flow))
      {
        addOutOfTreeNode (&(p->adjacencyList)[tempNode->arcToParent->to], tempNode->arcToParent);
      }

      for (j=0; j<tempNode->numOutOfTree; ++j) 
      {
        if (!tempNode->outOfTree[j]->flow) 
        {
          -- tempNode->numOutOfTree;
          tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
          -- j;
        }
      }

      sort(tempNode);
    }
  }

  for (i=0; i<(p->numNodes); ++i) 
  {
    tempNode = &(p->adjacencyList)[i];
    while (tempNode->excess > 0) 
    {
      ++ iteration;
      decompose(tempNode, (p->source), &iteration);
    }
  }
}


static void
displayBreakpoints (CutProblem *p, void)
{
  int i;
  for (i=0; i<(p->numNodes); ++i)
  {
    printf ("(p->n) %d %d\n", (i+1), (p->adjacencyList)[i].breakpoint);
  }
}

static void
freeMemory (CutProblem *p, void)
{
  int i;

  for (i=0; i<(p->numNodes); ++i)
  {
    freeRoot (&strongRoots[i]);
  }

  free (strongRoots);

  for (i=0; i<(p->numNodes); ++i)
  {
    if ((p->adjacencyList)[i].outOfTree)
    {
      free ((p->adjacencyList)[i].outOfTree);
    }
  }

  free ((p->adjacencyList));

  free ((p->labelCount));

  free ((p->arcList));

  free(degrees);
  free(weights);
  free((p->inSourceSet));
  free((p->bestSourceSet));
  free((p->invMapping));
  
}

void printHelp(int argc, char *argv[])
{
  printf("Usage : %s [OPTIONS]                                        \n\(p->n)", argv[0]);
  printf("Options:\n");

  printf("  --help                 print this help message                \n");
  printf("  --accuracy N           set the accuracy to N decimal places   \n");
  printf("                         note that a big N may induce errors on \n");
  printf("                         graphs that are big or have big weights\n");
  printf("                         by default, 4 decimal places           \n");
  printf("  --injectLambda L       start incremental procedure with L     \n");
  //printf("  --(p->weightedEdges)        enable if input has weights on edges   \n");
  //printf("  --(p->weightedNodes)        enable if input has weights on nodes   \n");
  printf("  --dumpSourceSet FILE   dump list of nodes in optimal solution \n");
  printf("                         to FILE                                \n");
  printf("  --(p->seedSet) ID           output solution is a subset of the     \n");
  printf("                         nodes with (p->partition) distinct to ID    \n");

  printf("\n\nNote that this program read from stdin\(p->n)");
  printf("An example command is \'%s < mygraph.txt\' to read from file\n", argv[0]);
  printf("\n");
  printf("The format of the input is as follows: \n");
  printf("\n");
  printf("N M\n");
  printf("[WEIGHT_NODE_1]\n");
  printf("[WEIGHT_NODE_2]\n");
  printf("...\n");
  printf("[WEIGHT_NODE_N]\n");
  printf("FROM_EDGE_1 TO_EDGE_1 [WEIGHT_EDGE_1]\n");
  printf("FROM_EDGE_2 TO_EDGE_2 [WEIGHT_EDGE_2]\n");
  printf("...\n");
  printf("FROM_EDGE_M TO_EDGE_M [WEIGHT_EDGE_M]\n");
  printf("\n");
  printf("Remember that for weighted graphs, options --(p->weightedEdges) \n");
  printf("and/or --(p->weightedNodes) must be used.  \n");
}

void parseParameters(CutProblem *p, int argc, char *argv[])
{
  int i = 0;
  for( i=3; i<argc; i++)
  {
    if(strcmp(argv[i], "--help")==0)
    {
      printHelp(argc, argv);
      exit(0);
    }
    else if (strcmp(argv[i], "--accuracy")==0 )
    {
      int accuracy  = atoi(argv[++i]);
      int z=0;
      (p->APP_VAL) = 1;
      for( z=0; z<accuracy; z++)
      {
        (p->APP_VAL) *=10LL;
      }
    }
    else if (strcmp(argv[i], "--injectLambda")==0 )
    {
      (p->injectedLambda) = atof(argv[++i] );
			(p->isLambdaInjected) = 1;
    }
    else if (strcmp(argv[i], "--(p->weightedEdges)") == 0)
    {
      (p->weightedEdges) = 1;
    }
    else if (strcmp(argv[i], "--(p->weightedNodes)") == 0)
    {
      (p->weightedNodes) = 1;
    }
    else if (strcmp(argv[i], "--dumpSourceSet") == 0)
		{
			dumpSourceSetFile = fopen( argv[++i], "w");
		}
    else if (strcmp(argv[i], "--(p->seedSet)") == 0)
		{
      (p->seedSet) = atoi(argv[++i]);
		}
    else
    {
      printf("%s: invalid argument %s\n", argv[0], argv[1]);
      printf("Try \'%s --help\' for more information.\n", argv[0]); 
      exit(-1);
    }

  }
}


int 
main(int argc, char ** argv) 
{

  if (argc < 3)
  {
    fprintf(stderr, "Error, not enough arguments provided\n");
    fprintf(stderr, "Usage: \'%s GRAPH_FILE PARTITION_FILE [OPTIONS]\'\n", argv[0]);
    fprintf(stderr, "Try \'%s --help\' for more information\n", argv[0]);
    exit(0xbeef);
  }

	printf ("c Incremental cut procedure for minimum conductance*\n");
	printf ("c Input graph file: %s\n", argv[1]);
	printf ("c Input (p->partition) file: %s\n", argv[2]);

  FILE *graphFile = fopen(argv[1], "r");
  FILE *partitionFile = fopen(argv[2], "r");

  parseParameters(argc, argv);


  //double thetime = timer();
  //readGraphFile();

  readMetisFormatGraph( graphFile, partitionFile);

  fclose(graphFile);
  fclose(partitionFile);
#ifdef PROGRESS
  printf ("c Finished reading file.\n"); fflush (stdout);
#endif

  simpleInitialization ();

#ifdef PROGRESS
  printf ("c Finished initialization.\n"); fflush (stdout);
#endif

  double thetime = timer();
#ifdef SIMPLE_PARAMETRIC	
  printf ("c Using simple parametric.\n"); fflush (stdout);
	pseudoflowPhase1();
  displayBreakpoints ();
#else
  //(p->initTime) = timer()-thetime;
  thetime = timer();
  incrementalCut();
  double incrementalCutTime = timer() - thetime;
  printf("c Input read time : %lf\n", (p->readTime));
  printf("c Parametric Graph initialization time : %lf\n", (p->initTime));
  printf("c Incremental cut time : %lf\n", incrementalCutTime);
#endif

#ifdef PROGRESS
  printf ("c Finished phase 1.\n"); fflush (stdout);
#endif


#ifdef RECOVER_FLOW
  recoverFlow();
  checkOptimality ();
#endif

  printf ("c Number of nodes     : %d\n", (p->numNodes));
  printf ("c Number of arcs      : %d\n", (p->numArcs));
#ifdef STATS
  printf ("c Number of arc scans : %lld\n", (p->numArcScans));
  printf ("c Number of mergers   : %d\n", (p->numMergers));
  printf ("c Number of pushes    : %lld\n", (p->numPushes));
  printf ("c Number of relabels  : %d\n", (p->numRelabels));
  printf ("c Number of gaps      : %d\n", (p->numGaps));
#endif

#ifdef BREAKPOINTS
  displayBreakpoints ();
#endif

  freeMemory ();

  return 0;
}

