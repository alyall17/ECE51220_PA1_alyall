#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <sys/time.h>

// Node of strictly-binary RC tree. Matches the student's plan.
typedef struct Node {
    int isLeaf;        // 1 if leaf
    int label;         // sink label if leaf
    double cap;        // sink capacitance if leaf
    // wire lengths to children (units: same as input file)
    double wireLeft;
    double wireRight;
    int numInverters;  // number of parallel inverters placed here (0 = none)
    struct Node *left;
    struct Node *right;
    struct Node *parent;
    // computed / cached values
    double cPrime;     // c' at this node (includes half-edge caps and sink). Driver Cout handled separately
    double subtreeC;   // sum of cPrime over subtree rooted at this node
    double rRoot;      // resistance from source to this node (includes driver Rb at root)
} Node;

// Inverter and wire parameter containers (Step 1)
typedef struct {
    double Cin; // input capacitance (F)
    double Cout; // output capacitance (F)
    double Rb;   // output resistance (Ohm)
} Inverter;

typedef struct {
    double r; // resistance per unit length (Ohm / unit)
    double c; // capacitance per unit length (F / unit)
} Wire;

// helpers
static Node *make_leaf(int label, double cap) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->isLeaf = 1;
    n->label = label;
    n->cap = cap;
    n->numInverters = 0;
    return n;
}

static Node *make_internal(Node *left, Node *right, double llen, double rlen) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->isLeaf = 0;
    n->left = left; n->right = right;
    n->wireLeft = llen; n->wireRight = rlen;
    n->numInverters = 0;
    if (left) left->parent = n;
    if (right) right->parent = n;
    return n;
}

static void free_tree(Node *n) {
    if (!n) return;
    free_tree(n->left);
    free_tree(n->right);
    free(n);
}

// compute cprime and subtree sums in post-order
// Compute c' and subtree sums in post-order (Step 3). We assume a first-order
// wire model where each edge contributes Ce = c * length and the node picks
// up half of each adjacent edge (as in the assignment description). The root
// receives the driver's output capacitance Cout.
// compute c' and subtree sums in post-order (half-edge allocation)
static void computeCPrimes(Node *n, const Wire *wire, const Inverter *drv) {
    if (!n) return;
    (void)drv; // drv parameter not used here but kept for API compatibility
    // reset cached values to avoid accumulation if this is called multiple times
    n->cPrime = 0.0;
    n->subtreeC = 0.0;
    computeCPrimes(n->left, wire, drv);
    computeCPrimes(n->right, wire, drv);
    // Half-edge capacitance allocation: each edge's Ce = wire->c * length
    // contributes half to the parent node and half to the child node.
    // Children were already processed, so add the child's half to its
    // cprime/subtree, and add the parent's half to the current node's cp.
    double cp = 0.0;
    if (n->left) {
        double Ce_left = wire->c * n->wireLeft;
        double half = Ce_left * 0.5;
        // add half to child
        n->left->cPrime += half;
        n->left->subtreeC += half;
        // add half to current node
        cp += half;
    }
    if (n->right) {
        double Ce_right = wire->c * n->wireRight;
        double half = Ce_right * 0.5;
        n->right->cPrime += half;
        n->right->subtreeC += half;
        cp += half;
    }
    if (n->isLeaf) cp += n->cap;
    n->cPrime = cp;
    n->subtreeC = cp + (n->left ? n->left->subtreeC : 0.0) + (n->right ? n->right->subtreeC : 0.0);
}

    // count total number of inverters placed in the tree
    static int countTotalInverters(Node *n) {
        if (!n) return 0;
        int sum = n->numInverters;
    sum += countTotalInverters(n->left);
    sum += countTotalInverters(n->right);
        return sum;
    }

// add edge contributions along path: helper that searches for target leaf and
// accumulates R_edge * subtree_c(child) when unwinding. Returns 1 if found.
// Add edge contributions R(u,v) * sum_{k in T_v} c'_k for each edge on the
// path from root to target. This recursively searches for target and when
// unwinding adds the child's subtree capacitance times the edge resistance.
// write pre-order topology to text file
// Write pre-order topology: matches output #1 format (Step 5).
// Internal nodes: "(lenLeft lenRight)"; Leaf: "label(cap)" per line.
static void writePreorderTopology(FILE *f, Node *n) {
    if (!n) return;
    if (n->isLeaf) {
        fprintf(f, "%d(%.10le)\n", n->label, n->cap);
        return;
    }
    fprintf(f, "(%.10le %.10le)\n", n->wireLeft, n->wireRight);
    writePreorderTopology(f, n->left);
    writePreorderTopology(f, n->right);
}
/* collectNodesPre removed: computeWorstDelayAndLabel now traverses tree iteratively
   so a separate node array is not required. */

// set Rroot for node and all descendants (Rroot at root should be set before calling)
static void setRRootRecursive(Node *n, const Wire *wire) {
    if (!n) return;
    if (n->left) {
        n->left->rRoot = n->rRoot + wire->r * n->wireLeft;
        setRRootRecursive(n->left, wire);
    }
    if (n->right) {
        n->right->rRoot = n->rRoot + wire->r * n->wireRight;
        setRRootRecursive(n->right, wire);
    }
}



// Shared stack buffer used by elmoreFromDriver to avoid repeated malloc/realloc/free.
// This is a simple, single-threaded optimization to reduce allocator churn.
typedef struct { Node *n; double accum; } StackEntry;
static StackEntry *elmore_shared_stack = NULL;
static size_t elmore_shared_cap = 0;

// Compute Elmore delays from driver node "drv_node" to every leaf in its subtree.
// Returns max delay and sets worst_leaf_out. Uses inv params and wire.
static double elmoreFromDriver(Node *drv_node, const Wire *wire, const Inverter *inv, Node **worst_leaf_out) {
    double max_delay = -1.0;
    Node *worst = NULL;
    if (!drv_node) { if (worst_leaf_out) *worst_leaf_out = NULL; return -1.0; }
    int k = drv_node->numInverters > 0 ? drv_node->numInverters : 1;
    double Rb_eff = inv->Rb / (double)k;
    double Cout_eff = inv->Cout * (double)k;
    double driver_total_c = drv_node->subtreeC + Cout_eff;

    // ensure shared stack is allocated
    if (elmore_shared_cap == 0) {
        elmore_shared_cap = 256;
        elmore_shared_stack = malloc(elmore_shared_cap * sizeof(StackEntry));
        if (!elmore_shared_stack) { fprintf(stderr, "memory allocation failure\n"); return -1.0; }
    }
    size_t sz = 0;
    double base = Rb_eff * driver_total_c;
    // push root
    elmore_shared_stack[sz++] = (StackEntry){ drv_node, base };
    while (sz) {
        StackEntry e = elmore_shared_stack[--sz];
        Node *n = e.n;
        double accum = e.accum;
        if (n->isLeaf) {
            double delay = accum;
            if (delay > max_delay) { max_delay = delay; worst = n; }
            continue;
        }
        if (n->right) {
            double add = wire->r * n->wireRight * n->right->subtreeC;
            if (sz == elmore_shared_cap) {
                size_t newcap = elmore_shared_cap * 2;
                StackEntry *tmp = realloc(elmore_shared_stack, newcap * sizeof(StackEntry));
                if (!tmp) { fprintf(stderr, "memory allocation failure\n"); return max_delay; }
                elmore_shared_stack = tmp; elmore_shared_cap = newcap;
            }
            elmore_shared_stack[sz++] = (StackEntry){ n->right, accum + add };
        }
        if (n->left) {
            double add = wire->r * n->wireLeft * n->left->subtreeC;
            if (sz == elmore_shared_cap) {
                size_t newcap = elmore_shared_cap * 2;
                StackEntry *tmp = realloc(elmore_shared_stack, newcap * sizeof(StackEntry));
                if (!tmp) { fprintf(stderr, "memory allocation failure\n"); return max_delay; }
                elmore_shared_stack = tmp; elmore_shared_cap = newcap;
            }
            elmore_shared_stack[sz++] = (StackEntry){ n->left, accum + add };
        }
    }
    if (worst_leaf_out) *worst_leaf_out = worst;
    return max_delay;
}

// Write binary elmore file for leaves in preorder by traversing the tree once from the root
// Reuse the file-scoped elmore_shared_stack buffer to avoid extra allocations.
static void writeElmoreFile(FILE *f, Node *root, const Wire *wire, const Inverter *inv) {
    if (!f || !root) return;
    int k = root->numInverters > 0 ? root->numInverters : 1;
    double Rb_eff = inv->Rb / (double)k;
    double Cout_eff = inv->Cout * (double)k;
    double driver_total_c = root->subtreeC + Cout_eff;

    // ensure shared stack is allocated
    if (elmore_shared_cap == 0) {
        elmore_shared_cap = 256;
        elmore_shared_stack = malloc(elmore_shared_cap * sizeof(StackEntry));
        if (!elmore_shared_stack) { fprintf(stderr, "memory allocation failure\n"); return; }
    }
    size_t sz = 0;
    double base = Rb_eff * driver_total_c;
    elmore_shared_stack[sz++] = (StackEntry){ root, base };
    while (sz) {
        StackEntry e = elmore_shared_stack[--sz];
        Node *n = e.n; double accum = e.accum;
        if (n->isLeaf) {
            int lab = n->label; double delay = accum;
            fwrite(&lab, sizeof(int), 1, f);
            fwrite(&delay, sizeof(double), 1, f);
            continue;
        }
        // push right then left so left visited before right
        if (n->right) {
            double add = wire->r * n->wireRight * n->right->subtreeC;
            if (sz == elmore_shared_cap) {
                size_t newcap = elmore_shared_cap * 2;
                StackEntry *tmp = realloc(elmore_shared_stack, newcap * sizeof(StackEntry));
                if (!tmp) { fprintf(stderr, "memory allocation failure\n"); return; }
                elmore_shared_stack = tmp; elmore_shared_cap = newcap;
            }
            elmore_shared_stack[sz++] = (StackEntry){ n->right, accum + add };
        }
        if (n->left) {
            double add = wire->r * n->wireLeft * n->left->subtreeC;
            if (sz == elmore_shared_cap) {
                size_t newcap = elmore_shared_cap * 2;
                StackEntry *tmp = realloc(elmore_shared_stack, newcap * sizeof(StackEntry));
                if (!tmp) { fprintf(stderr, "memory allocation failure\n"); return; }
                elmore_shared_stack = tmp; elmore_shared_cap = newcap;
            }
            elmore_shared_stack[sz++] = (StackEntry){ n->left, accum + add };
        }
    }
}

// Greedy inverter insertion top-down: insert inverter at offending child of driver until all stage delays <= constraint.
// This places inverters at existing internal nodes (no wire splitting). It increments num_inverters at a node when inserting.
// forward declaration: compute worst delay across drivers (defined later)
static double computeWorstDelayAndLabel(Node *root, const Wire *wire, const Inverter *inv, int *worstLabelOut);

// add (or remove when dC is negative) capacitance to node->cPrime and propagate to all ancestors' subtreeC
static void addCapToAncestors(Node *node, double dC) {
    if (!node || dC == 0.0) return;
    node->cPrime += dC;
    Node *p = node;
    while (p) {
        p->subtreeC += dC;
        p = p->parent;
    }
}

static int greedyInsertInverters(Node *root, const Wire *wire, const Inverter *inv, double constraint, int debug) {
    // ensure root has one implicit driver
    if (root->numInverters == 0) root->numInverters = 1;

    // driver worklist: simple dynamic array of nodes to check
    Node **drivers = NULL; size_t dcnt = 0, dcap = 0;
    // ensure initial allocation
    dcap = 16; drivers = malloc(dcap * sizeof(Node*));
    if (!drivers) { fprintf(stderr, "memory allocation failure\n"); return 0; }
    drivers[dcnt++] = root;
    int inserted = 0;

    for (size_t di = 0; di < dcnt; ++di) {
        Node *drv = drivers[di];
        Node *worst = NULL;
        double drvMax = elmoreFromDriver(drv, wire, inv, &worst);
        if (drvMax <= constraint) continue;

    // compute current global worst delay as baseline
    int dummyLabel = -1;
    double globalBefore = computeWorstDelayAndLabel(root, wire, inv, &dummyLabel);
    // also compute driver's local Elmore before trials
    /* driver's local elmore recomputation not needed here (we recompute global baseline) */

        // build path nodes from child of drv down to worst (inclusive)
        // walk up from worst to drv (exclusive) and collect nodes
        Node **path = NULL; size_t pcap = 0, psz = 0;
        Node *p = worst;
        while (p && p != drv) {
            if (psz == pcap) {
                pcap = pcap ? pcap * 2 : 16;
                Node **tmp = realloc(path, pcap * sizeof(Node*));
                if (!tmp) { free(path); free(drivers); fprintf(stderr, "memory allocation failure\n"); return inserted; }
                path = tmp;
            }
            path[psz++] = p;
            p = p->parent;
        }
        if (psz == 0) { free(path); continue; }
        // reverse order so candidates start near drv and go toward leaf
        for (size_t i = 0; i < psz/2; ++i) {
            Node *tmp = path[i]; path[i] = path[psz-1-i]; path[psz-1-i] = tmp;
        }

        // try each candidate on path: temporarily add 1 or 2 inverters (2-step lookahead)
        double bestGlobal = globalBefore;
        Node *bestCand = NULL;
        int bestK = 0;
        // configurable lookahead: default 4, can be overridden with PA1_LOOKAHEAD env var
        int maxLookahead = 4;
        char *lookEnv = getenv("PA1_LOOKAHEAD");
        if (lookEnv && lookEnv[0] != '\0') {
            int v = atoi(lookEnv);
            if (v > 0) maxLookahead = v;
        }
        for (size_t pi = 0; pi < psz; ++pi) {
            Node *cand = path[pi];
            for (int ktry = 1; ktry <= maxLookahead; ++ktry) {
                // Apply temporary capacitance change for the trial: each inverter adds inv->Cin to the input node, and
                // placing k inverters in parallel multiplies that by k. We update cand->cPrime and propagate to
                // subtreeC for all ancestors so computeWorstDelayAndLabel and elmoreFromDriver see the change.
                double dC = inv->Cin * (double)ktry;
                addCapToAncestors(cand, dC);
                cand->numInverters += ktry;
                double trialGlobal = computeWorstDelayAndLabel(root, wire, inv, NULL);
                // driver's local Elmore after this trial
                (void)elmoreFromDriver(drv, wire, inv, NULL);
                // revert temporary changes
                cand->numInverters -= ktry;
                addCapToAncestors(cand, -dC);
                if (trialGlobal < bestGlobal) {
                    bestGlobal = trialGlobal;
                    bestCand = cand;
                    bestK = ktry;
                }
            }
        }

        if (bestCand && bestK > 0) {
            // commit best candidate with bestK inverters -- apply capacitance permanently
            double dCcommit = inv->Cin * (double)bestK;
            addCapToAncestors(bestCand, dCcommit);
            bestCand->numInverters += bestK;
            inserted += bestK;
            if (debug) fprintf(stderr, "  committed candidate ptr=%p (leaf=%d label=%d) k=%d newGlobal=%.12e\n", (void*)bestCand, bestCand->isLeaf, bestCand->isLeaf ? bestCand->label : -1, bestK, bestGlobal);
            // add committed node as new driver to process later
            if (dcnt == dcap) {
                size_t ncap = dcap * 2;
                Node **tmp = realloc(drivers, ncap * sizeof(Node*));
                if (!tmp) { free(path); free(drivers); fprintf(stderr, "memory allocation failure\n"); return inserted; }
                drivers = tmp; dcap = ncap;
            }
            drivers[dcnt++] = bestCand;
        } else {
            if (debug) fprintf(stderr, "  no candidate reduced global worst (bestGlobal=%.12e, globalBefore=%.12e)\n", bestGlobal, globalBefore);
        }
        free(path);
    }
    free(drivers);
    return inserted;
}

// Ensure every leaf is non-inverting: total number of inverters along path (including root implicit) must be even.
// Root counts as 1 stage (implicit driver). So we require (1 + sum(num_inverters on path)) % 2 == 0 => sum %2 == 1.
// If a leaf path has wrong parity, insert one inverter at its parent.
static int parityFix(Node *root) {
    // traverse all leaves
    if (!root) return 0;
    // collect leaves by traversal
    Node **stack = NULL; size_t sz = 0, cap = 0;
    cap = 32; stack = malloc(cap * sizeof(Node*));
    if (!stack) { fprintf(stderr, "memory allocation failure\n"); return 0; }
    stack[sz++] = root;
    int inserted = 0;
    while (sz) {
        Node *n = stack[--sz];
        if (n->isLeaf) {
            // compute sum numInverters along path from root
            int sum = 0;
            Node *p = n;
            while (p) { sum += p->numInverters; p = p->parent; }
            // total number of inverters along path is sum, need total to be even
            if ((sum % 2) != 0) {
                Node *par = n->parent;
                if (par) {
                    // Only increment if this will change the parent's parity (avoid repeated increments)
                    // i.e., only add one inverter if parent's count is currently even.
                    if ((par->numInverters % 2) == 0) { par->numInverters += 1; inserted += 1; }
                } else {
                    if ((n->numInverters % 2) == 0) { n->numInverters += 1; inserted += 1; }
                }
            }
            continue;
        }
        if (n->right) {
            if (sz == cap) {
                size_t ncap = cap * 2;
                Node **tmp = realloc(stack, ncap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return inserted; }
                stack = tmp; cap = ncap;
            }
            stack[sz++] = n->right;
        }
        if (n->left) {
            if (sz == cap) {
                size_t ncap = cap * 2;
                Node **tmp = realloc(stack, ncap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return inserted; }
                stack = tmp; cap = ncap;
            }
            stack[sz++] = n->left;
        }
    }
    free(stack);
    return inserted;
}

// compute the worst Elmore delay across all current drivers (nodes with numInverters>0)
static double computeWorstDelayAndLabel(Node *root, const Wire *wire, const Inverter *inv, int *worstLabelOut) {
    double maxd = -1.0;
    int worstLabel = -1;
    if (!root) { if (worstLabelOut) *worstLabelOut = -1; return -1.0; }
    // iterative pre-order stack traversal to avoid allocating a node array each call
    size_t cap = 64, sz = 0;
    Node **stack = malloc(cap * sizeof(Node*));
    if (!stack) { fprintf(stderr, "memory allocation failure\n"); return -1.0; }
    stack[sz++] = root;
    while (sz) {
        Node *n = stack[--sz];
        if (n->numInverters > 0) {
            Node *worstLeaf = NULL;
            double d = elmoreFromDriver(n, wire, inv, &worstLeaf);
            if (d > maxd) {
                maxd = d;
                worstLabel = worstLeaf ? worstLeaf->label : -1;
            }
        }
        if (n->right) {
            if (sz == cap) { size_t ncap = cap * 2; Node **tmp = realloc(stack, ncap * sizeof(Node*)); if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return maxd; } stack = tmp; cap = ncap; }
            stack[sz++] = n->right;
        }
        if (n->left) {
            if (sz == cap) { size_t ncap = cap * 2; Node **tmp = realloc(stack, ncap * sizeof(Node*)); if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return maxd; } stack = tmp; cap = ncap; }
            stack[sz++] = n->left;
        }
    }
    free(stack);
    if (worstLabelOut) *worstLabelOut = worstLabel;
    return maxd;
}

// iterate greedy insertion + parity fix until no change in total inverter count
// debug: if non-zero, print per-iteration diagnostics to stderr
static int iterateInsertionUntilConverged(Node *root, const Wire *wire, const Inverter *inv, double constraint, int debug) {
    int it = 0;
    int noImproveLimit = 50; // default no-improve iterations
    char *envNo = getenv("PA1_NO_IMPROVE_ITERS");
    if (envNo && envNo[0] != '\0') { int v = atoi(envNo); if (v > 0) noImproveLimit = v; }
    int noImproveCounter = 0;
    double bestWorst = 1e300;
    // wall-clock timeout (seconds)
    int timeoutSecs = 360; // default 6 minutes
    char *envT = getenv("PA1_TIMEOUT");
    if (envT && envT[0] != '\0') { int v = atoi(envT); if (v > 0) timeoutSecs = v; }
    double t0 = 0.0;
    // get current time
    struct timeval tv0; gettimeofday(&tv0, NULL); t0 = (double)tv0.tv_sec + (double)tv0.tv_usec * 1e-6;

    while (1) {
        int before = countTotalInverters(root);
        greedyInsertInverters(root, wire, inv, constraint, debug);
        parityFix(root);
        int after = countTotalInverters(root);
        int worstLabel = -1;
        double worstDelay = computeWorstDelayAndLabel(root, wire, inv, &worstLabel);
        if (debug) {
            fprintf(stderr, "iter %d: totalInverters before=%d after=%d worstDelay=%.12e worstLeaf=%d\n", it, before, after, worstDelay, worstLabel);
        }
        // handle improvement tracking
        if (worstDelay < bestWorst - 1e-18) {
            bestWorst = worstDelay;
            noImproveCounter = 0;
        } else {
            noImproveCounter++;
        }
        // check no-improve stop
        if (noImproveCounter >= noImproveLimit) {
            if (debug) fprintf(stderr, "stopping: no improvement for %d iterations\n", noImproveCounter);
            return 0;
        }
        // check timeout
        struct timeval tv; gettimeofday(&tv, NULL); double now = (double)tv.tv_sec + (double)tv.tv_usec * 1e-6;
        if (now - t0 > (double)timeoutSecs) {
            fprintf(stderr, "stopping: timeout after %.0f seconds\n", now - t0);
            return 1;
        }
        if (after == before) return 0; // converged
        ++it;
    }
}

// post-order print topology with inverter counts: internal nodes printed as (lenL lenR k)
// Leaves printed as label(cap). This matches output #3 format.
static void writePostorderTopology(FILE *f, Node *n) {
    if (!n) return;
    if (n->isLeaf) {
        fprintf(f, "%d(%.10le)\n", n->label, n->cap);
        return;
    }
    writePostorderTopology(f, n->left);
    writePostorderTopology(f, n->right);
    // print node with its inverter count
    fprintf(f, "(%.10le %.10le %d)\n", n->wireLeft, n->wireRight, n->numInverters);
}

// binary post-order topology writer: leaf => int label, double cap; internal => int -1, double lenL, double lenR, int k
static void writePostorderTopologyBinary(FILE *f, Node *n) {
    if (!n) return;
    if (n->isLeaf) {
        int lab = n->label;
        fwrite(&lab, sizeof(int), 1, f);
        fwrite(&n->cap, sizeof(double), 1, f);
        return;
    }
    writePostorderTopologyBinary(f, n->left);
    writePostorderTopologyBinary(f, n->right);
    int marker = -1;
    fwrite(&marker, sizeof(int), 1, f);
    fwrite(&n->wireLeft, sizeof(double), 1, f);
    fwrite(&n->wireRight, sizeof(double), 1, f);
    fwrite(&n->numInverters, sizeof(int), 1, f);
}


int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "Usage: %s time_constraint inv.param wire.param tree.post in.pre out.elmore out.ttopo out.btopo\n", argv[0]);
        return EXIT_FAILURE;
    }

    double time_constraint = atof(argv[1]);

    const char *inv_param = argv[2];
    const char *wire_param = argv[3];
    const char *tree_in = argv[4];
    const char *pre_out = argv[5];
    const char *elmore_out = argv[6];
    const char *ttopo_out = argv[7];
    const char *btopo_out = argv[8];

    // read inverter params
    double Cin=0.0, Cout=0.0, Rb=0.0;
    FILE *paramFile = fopen(inv_param, "r");
    if (!paramFile) { perror("inv.param"); return EXIT_FAILURE; }
    if (fscanf(paramFile, "%le %le %le", &Cin, &Cout, &Rb) != 3) { fclose(paramFile); fprintf(stderr, "bad inv.param\n"); return EXIT_FAILURE; }
    fclose(paramFile);

    // read wire params
    double rPerLen=0.0, cPerLen=0.0;
    FILE *wireFile = fopen(wire_param, "r");
    if (!wireFile) { perror("wire.param"); return EXIT_FAILURE; }
    if (fscanf(wireFile, "%le %le", &rPerLen, &cPerLen) != 2) { fclose(wireFile); fprintf(stderr, "bad wire.param\n"); return EXIT_FAILURE; }
    fclose(wireFile);

    // read post-order tree and build via stack
    FILE *treeFile = fopen(tree_in, "r");
    if (!treeFile) { perror("tree input"); return EXIT_FAILURE; }

    Node **parseStack = NULL;
    size_t stackSz = 0;
    size_t stackCap = 0;
    char line[512];
    while (fgets(line, sizeof(line), treeFile)) {
        // strip leading spaces
        char *s = line;
        while (*s==' '||*s=='\t' || *s=='\r' || *s=='\n') s++;
        if (*s=='\0') continue;
        // detect leaf: starts with digit
        if ((s[0] >= '0' && s[0] <= '9') || s[0]=='-') {
            int label = 0; double cap = 0.0;
            if (sscanf(s, "%d(%lf)", &label, &cap) == 2) {
                Node *n = make_leaf(label, cap);
                if (!n) { fclose(treeFile); return EXIT_FAILURE; }
                if (stackSz == stackCap) {
                    size_t newCap = stackCap ? stackCap*2 : 16;
                    Node **tmp = realloc(parseStack, newCap * sizeof(Node*));
                    if (!tmp) { fprintf(stderr, "memory allocation failure\n"); fclose(treeFile); return EXIT_FAILURE; }
                    parseStack = tmp; stackCap = newCap;
                }
                parseStack[stackSz++] = n;
                continue;
            }
        }
        // otherwise expect internal node like: (%.10le %.10le)
        double l=0.0, r=0.0;
        if (sscanf(s, "(%lf %lf)", &l, &r) == 2) {
            // pop right then left (post-order)
            if (stackSz < 2) { fprintf(stderr, "malformed tree file: not enough children\n"); fclose(treeFile); return EXIT_FAILURE; }
            Node *right = parseStack[--stackSz];
            Node *left = parseStack[--stackSz];
            Node *n = make_internal(left, right, l, r);
            if (!n) { fclose(treeFile); return EXIT_FAILURE; }
            if (stackSz == stackCap) {
                size_t newCap = stackCap ? stackCap*2 : 16;
                Node **tmp = realloc(parseStack, newCap * sizeof(Node*));
                if (!tmp) { fprintf(stderr, "memory allocation failure\n"); fclose(treeFile); return EXIT_FAILURE; }
                parseStack = tmp; stackCap = newCap;
            }
            parseStack[stackSz++] = n;
            continue;
        }
        // no alternative formats supported; ignore unknown lines
    }
    fclose(treeFile);

    if (stackSz != 1) {
        fprintf(stderr, "unexpected stack size after parsing: %zu\n", stackSz);
        for (size_t i=0;i<stackSz;i++) free_tree(parseStack[i]);
        free(parseStack);
        return EXIT_FAILURE;
    }
    Node *root = parseStack[0];
    free(parseStack);

    // compute cprimes and subtree sums
    Wire wire;
    wire.r = rPerLen;
    wire.c = cPerLen;
    Inverter inv;
    inv.Cin = Cin;
    inv.Cout = Cout;
    inv.Rb = Rb;
    computeCPrimes(root, &wire, &inv);

    // compute Elmore delays for leaves (pre-order requirement)
    //prepare pre-order topology file
    FILE *fpre = fopen(pre_out, "w");
    if (!fpre) { perror("pre_out"); free_tree(root); return EXIT_FAILURE; }
    writePreorderTopology(fpre, root);
    fclose(fpre);

    // write binary elmore file (pre-order leaf order)
    FILE *elmoreFile = fopen(elmore_out, "wb");
    if (!elmoreFile) { perror("elmore_out"); free_tree(root); return EXIT_FAILURE; }

    // Prepare nodes array and compute Rroot for each node (resistance from source to node).
    // Rroot at root should include driver Rb. We compute Rroot in a pre-order traversal.
    // compute Rroot: resistance from source to node. Start from root (Rb included)
    // and propagate down adding edge resistances.
    root->rRoot = Rb; // source -> root includes driver Rb
    setRRootRecursive(root, &wire);
    // write elmore delays for leaves efficiently (single traversal)
    writeElmoreFile(elmoreFile, root, &wire, &inv);
    fclose(elmoreFile);

    // Now perform inverter insertion (greedy + parity) iteratively until convergence
    int debug = 0;
    char *dbg = getenv("PA1_DEBUG");
    if (dbg && dbg[0] != '\0') debug = 1;
    int iter_result = iterateInsertionUntilConverged(root, &wire, &inv, time_constraint, debug);
    if (iter_result) fprintf(stderr, "warning: inverter insertion reached iteration limit before converging\n");

    // Write post-order topology text and binary files
    FILE *ftt = fopen(ttopo_out, "w");
    FILE *fbt = fopen(btopo_out, "wb");
    if (!ftt || !fbt) {
        if (ftt) fclose(ftt);
        if (fbt) fclose(fbt);
        // leave them empty if we couldn't open
        free_tree(root);
        return EXIT_FAILURE;
    }
    writePostorderTopology(ftt, root);
    writePostorderTopologyBinary(fbt, root);
    fclose(ftt); fclose(fbt);

    free_tree(root);
    return EXIT_SUCCESS;
}
