#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

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
static int addPathContributions(Node *n, Node *target, const Wire *wire, double *accum) {
    if (!n) return 0;
    if (n == target) return 1;
    if (n->left) {
        if (addPathContributions(n->left, target, wire, accum)) {
            double Redge = wire->r * n->wireLeft;
            *accum += Redge * n->left->subtreeC;
            return 1;
        }
    }
    if (n->right) {
        if (addPathContributions(n->right, target, wire, accum)) {
            double Redge = wire->r * n->wireRight;
            *accum += Redge * n->right->subtreeC;
            return 1;
        }
    }
    return 0;
}

// find all leaves in pre-order and perform action via callback
typedef void (*leaf_cb)(Node *leaf, void *ctx);
static void preorderLeaves(Node *n, leaf_cb cb, void *ctx) {
    if (!n) return;
    if (n->isLeaf) {
        cb(n, ctx);
        return;
    }
    // internal: visit node (no-op for leaves), then left then right
    if (n->left) preorderLeaves(n->left, cb, ctx);
    if (n->right) preorderLeaves(n->right, cb, ctx);
}

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

// context for leaf writer
struct cb_ctx { FILE *fel; Node *root; const Wire *wire; double Rb; double inv_Cout; Node **all_nodes; size_t all_count; };

// helper: compute LCA by walking ancestors of a and marking in an array
// We implement a simple path-based LCA without extra memory by building
// the ancestor list of a and then walking up from b.
static Node *lca(Node *a, Node *b) {
    if (!a || !b) return NULL;
    // build ancestor list for a
    Node *cur = a;
    size_t cap = 64;
    size_t sz = 0;
    Node **anc = malloc(cap * sizeof(Node*));
    if (!anc) { fprintf(stderr, "memory allocation failure\n"); return NULL; }
    while (cur) {
        if (sz == cap) {
            size_t newCap = cap * 2;
            Node **tmp = realloc(anc, newCap * sizeof(Node*));
            if (!tmp) { free(anc); fprintf(stderr, "memory allocation failure\n"); return NULL; }
            anc = tmp; cap = newCap;
        }
        anc[sz++] = cur;
        cur = cur->parent;
    }
    // walk up from b and return first node that appears in anc
    Node *res = NULL;
    Node *p = b;
    while (p) {
        for (size_t i = 0; i < sz; ++i) if (anc[i] == p) { res = p; break; }
        if (res) break;
        p = p->parent;
    }
    free(anc);
    return res;
}

static void leafWriter(Node *leaf, void *vctx) {
    struct cb_ctx *c = (struct cb_ctx*)vctx;
    double delay = 0.0;
    // First-formula: sum over all nodes i of c'_i * Rcommon(i, leaf)
    // where Rcommon(i,leaf) = Rroot(LCA(i,leaf)).
    for (size_t k = 0; k < c->all_count; ++k) {
        Node *i = c->all_nodes[k];
        double ci = i->cPrime;
        if (ci == 0.0) continue;
        Node *L = lca(i, leaf);
        if (!L) continue;
        delay += ci * L->rRoot;
    }
    // include driver's output capacitance at the root as an extra c' term
    // multiplied by Rroot(root). Treat the driver as having at least one
    // stage (implicit) when computing effective Cout for the pre-output.
    double root_k = (double)(c->root->numInverters ? c->root->numInverters : 1);
    double Cout_eff = c->inv_Cout * root_k;
    delay += Cout_eff * c->root->rRoot;
    // write label (int) then double
    fwrite(&leaf->label, sizeof(int), 1, c->fel);
    fwrite(&delay, sizeof(double), 1, c->fel);
}

// collect nodes in pre-order into dynamic array *allp; *cntp and *allocp are updated
static void collectNodesPre(Node ***allp, size_t *cntp, size_t *allocp, Node *n) {
    if (!n) return;
    if (*cntp == *allocp) {
        *allocp = (*allocp == 0) ? 64 : (*allocp * 2);
        Node **tmp = realloc(*allp, (*allocp) * sizeof(Node*));
        if (!tmp) { fprintf(stderr, "memory allocation failure\n"); exit(EXIT_FAILURE); }
        *allp = tmp;
    }
    (*allp)[(*cntp)++] = n;
    collectNodesPre(allp, cntp, allocp, n->left);
    collectNodesPre(allp, cntp, allocp, n->right);
}

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

// find first child of ancestor "from" on the path to node "to"
static Node *firstChildOnPath(Node *from, Node *to) {
    // walk up from 'to' to find the node whose parent is 'from'
    Node *p = to;
    Node *prev = NULL;
    while (p && p != from) { prev = p; p = p->parent; }
    if (p == from) return prev; // prev is immediate child of from on path
    return NULL;
}

// Compute Elmore delays from driver node "drv_node" to every leaf in its subtree.
// Returns max delay and sets worst_leaf_out. Uses inv params and wire.
static double elmoreFromDriver(Node *drv_node, const Wire *wire, const Inverter *inv, Node **worst_leaf_out) {
    double max_delay = -1.0;
    Node *worst = NULL;
    // determine effective Rb and Cout at this driver based on num_inverters
    int k = drv_node->numInverters > 0 ? drv_node->numInverters : 1; // at least 1 when used as driver
    double Rb_eff = inv->Rb / (double)k;
    double Cout_eff = inv->Cout * (double)k;

    // driver_total_cap is drv_node->subtree_c plus driver output cap
    double driver_total_c = drv_node->subtreeC + Cout_eff;

    // For each leaf in subtree, compute delay = Rb_eff * driver_total_c + sum_edges Redge * subtree_c(child)
    // traverse subtree and collect leaves
    // simple stack traversal
    Node **stack = NULL; size_t sz = 0, cap = 0;
    //push drv_node
    cap = 16; stack = malloc(cap * sizeof(Node*)); stack[sz++] = drv_node;
    if (!stack) { fprintf(stderr, "memory allocation failure\n"); return -1.0; }
    while (sz) {
        Node *n = stack[--sz];
        if (n->isLeaf) {
            double delay = Rb_eff * driver_total_c;
            // add edge contributions along path from drv_node to this leaf
            addPathContributions(drv_node, n, wire, &delay);
            if (delay > max_delay) { max_delay = delay; worst = n; }
            continue;
        }
        if (n->right) {
            if (sz == cap) {
                cap *= 2;
                Node **tmp = realloc(stack, cap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return -1.0; }
                stack = tmp;
            }
            stack[sz++] = n->right;
        }
        if (n->left) {
            if (sz == cap) {
                cap *= 2;
                Node **tmp = realloc(stack, cap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return -1.0; }
                stack = tmp;
            }
            stack[sz++] = n->left;
        }
    }
    free(stack);
    if (worst_leaf_out) *worst_leaf_out = worst;
    return max_delay;
}

// Greedy inverter insertion top-down: insert inverter at offending child of driver until all stage delays <= constraint.
// This places inverters at existing internal nodes (no wire splitting). It increments num_inverters at a node when inserting.
static int greedyInsertInverters(Node *root, const Wire *wire, const Inverter *inv, double constraint) {
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
    double maxd = elmoreFromDriver(drv, wire, inv, &worst);
        if (maxd <= constraint) continue;
        // find child of drv on path to worst leaf
    Node *child = firstChildOnPath(drv, worst);
        if (!child) continue; // shouldn't happen
        // insert one inverter at child (increase parallel count)
    child->numInverters += 1;
        inserted += 1;
        // add child as a driver to be processed
        if (dcnt == dcap) {
            size_t ncap = dcap * 2;
            Node **tmp = realloc(drivers, ncap * sizeof(Node*));
            if (!tmp) { free(drivers); fprintf(stderr, "memory allocation failure\n"); return inserted; }
            drivers = tmp; dcap = ncap;
        }
    drivers[dcnt++] = child;
        // continue loop; the newly added driver will be processed later
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
                if (par) { par->numInverters += 1; inserted += 1; }
                else { n->numInverters += 1; inserted += 1; }
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

// iterate greedy insertion + parity fix until no change in total inverter count
static int iterateInsertionUntilConverged(Node *root, const Wire *wire, const Inverter *inv, double constraint) {
    const int MAX_ITERS = 64;
    for (int it = 0; it < MAX_ITERS; ++it) {
        int before = countTotalInverters(root);
        greedyInsertInverters(root, wire, inv, constraint);
        parityFix(root);
        int after = countTotalInverters(root);
        if (after == before) return 0; // converged
    }
    return 1; // reached iteration limit
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
                if (stackSz == stackCap) { stackCap = stackCap ? stackCap*2 : 16; parseStack = realloc(parseStack, stackCap * sizeof(Node*)); }
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
            if (stackSz == stackCap) { stackCap = stackCap ? stackCap*2 : 16; parseStack = realloc(parseStack, stackCap * sizeof(Node*)); }
            parseStack[stackSz++] = n;
            continue;
        }
        // try alternative formats
        if (sscanf(s, "%d ( %lf )", (int[]){0}, &l) == 0) {
            // ignore
        }
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
    // collect nodes into a dynamic array (pre-order) using helper
    size_t allocNodes = 0, nodeCount = 0;
    Node **allNodes = NULL;
    collectNodesPre(&allNodes, &nodeCount, &allocNodes, root);

    // compute Rroot: resistance from source to node. Start from root (Rb included)
    // and propagate down adding edge resistances.
    root->rRoot = Rb; // source -> root includes driver Rb
    // set rRoot for all nodes starting at root
    setRRootRecursive(root, &wire);

    struct cb_ctx ctx;
    ctx.fel = elmoreFile; ctx.root = root; ctx.wire = &wire; ctx.Rb = Rb; ctx.inv_Cout = inv.Cout; ctx.all_nodes = allNodes; ctx.all_count = nodeCount;
    preorderLeaves(root, leafWriter, &ctx);
    free(allNodes);
    fclose(elmoreFile);

    // Now perform inverter insertion (greedy + parity) iteratively until convergence
    int iter_result = iterateInsertionUntilConverged(root, &wire, &inv, time_constraint);
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
