/* pa1.c
 * Rewritten to follow the student's implementation plan.
 * Features implemented in this file:
 * - Data structures for Node, Inverter, and Wire (Step 1)
 * - Parsing functions for inverter, wire, and post-order tree (Step 2)
 * - RC parameter computations (Step 3)
 * - Elmore delay computation using the second formula (Step 4)
 * - Pre-order / post-order printers and binary writers (Step 5)
 * - A stub for inverter insertion (Step 6) — greedy algorithm to be implemented next
 *
/*
 * pa1.c
 * Rewritten to follow the student's implementation plan.
 * Features implemented in this file:
 * - Data structures for Node, Inverter, and Wire
 * - Parsing functions for inverter, wire, and post-order tree
 * - RC parameter computations
 * - Elmore delay computation (node-sum formula)
 * - Pre-order and post-order topology writers
 * - Greedy inverter insertion and parity fix (no wire-splitting)
 *
 * The file focuses on correctness and robustness of the core algorithm. It
 * intentionally does not implement wire-splitting repeaters (that is a
 * larger feature) and keeps the greedy insertion policy simple.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* Node of strictly-binary RC tree. Matches the user's plan. */
typedef struct Node {
    int is_leaf;        /* 1 if leaf */
    int label;          /* sink label if leaf */
    double cap;         /* sink capacitance if leaf */
    /* wire lengths to children (units: same as input file) */
    double wire_left;
    double wire_right;
    int num_inverters;  /* number of parallel inverters placed here (0 = none) */
    struct Node *left;
    struct Node *right;
    struct Node *parent;
    /* computed / cached values */
    double cprime;      /* c' at this node (includes half-edge caps, sink, and driver Cout at root) */
    double subtree_c;   /* sum of cprime over subtree rooted at this node */
    double Rroot;       /* resistance from source to this node (includes driver Rb at root) */
} Node;

/* Inverter and wire parameter containers (Step 1) */
typedef struct {
    double Cin; /* input capacitance (F) */
    double Cout;/* output capacitance (F) */
    double Rb;  /* output resistance (Ohm) */
} Inverter;

typedef struct {
    double r; /* resistance per unit length (Ohm / unit) */
    double c; /* capacitance per unit length (F / unit) */
} Wire;

/* helpers */
static Node *make_leaf(int label, double cap) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->is_leaf = 1;
    n->label = label;
    n->cap = cap;
    n->num_inverters = 0;
    return n;
}

static Node *make_internal(Node *left, Node *right, double llen, double rlen) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->is_leaf = 0;
    n->left = left; n->right = right;
    n->wire_left = llen; n->wire_right = rlen;
    n->num_inverters = 0;
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

/* compute cprime and subtree sums in post-order */
/* Compute c' and subtree sums in post-order (Step 3). We assume a first-order
 * wire model where each edge contributes Ce = c * length and the node picks
 * up half of each adjacent edge (as in the assignment description). The root
 * receives the driver's output capacitance Cout.
 */
static void compute_cprimes(Node *n, const Wire *wire, const Inverter *drv) {
    if (!n) return;
    compute_cprimes(n->left, wire, drv);
    compute_cprimes(n->right, wire, drv);
    /* Half-edge capacitance allocation: each edge's Ce = wire->c * length
     * contributes half to the parent node and half to the child node.
     * Children were already processed, so add the child's half to its
     * cprime/subtree, and add the parent's half to the current node's cp.
     */
    double cp = 0.0;
    if (n->left) {
        double Ce_left = wire->c * n->wire_left;
        double half = Ce_left * 0.5;
        /* add half to child */
        n->left->cprime += half;
        n->left->subtree_c += half;
        /* add half to current node */
        cp += half;
    }
    if (n->right) {
        double Ce_right = wire->c * n->wire_right;
        double half = Ce_right * 0.5;
        n->right->cprime += half;
        n->right->subtree_c += half;
        cp += half;
    }
    if (n->is_leaf) cp += n->cap;
    /* Do NOT lump driver Cout into cprime here; we account for driver Cout
     * explicitly when writing/elmore checks (ctx.inv_Cout used elsewhere).
     */
    n->cprime = cp;
    n->subtree_c = cp + (n->left ? n->left->subtree_c : 0.0) + (n->right ? n->right->subtree_c : 0.0);
}

/* add edge contributions along path: helper that searches for target leaf and
 * accumulates R_edge * subtree_c(child) when unwinding. Returns 1 if found. */
/* Add edge contributions R(u,v) * sum_{k in T_v} c'_k for each edge on the
 * path from root to target. This recursively searches for target and when
 * unwinding adds the child's subtree capacitance times the edge resistance.
 */
static int add_path_contributions(Node *n, Node *target, const Wire *wire, double *accum) {
    if (!n) return 0;
    if (n == target) return 1;
    if (n->left) {
        if (add_path_contributions(n->left, target, wire, accum)) {
            double Redge = wire->r * n->wire_left;
            *accum += Redge * n->left->subtree_c;
            return 1;
        }
    }
    if (n->right) {
        if (add_path_contributions(n->right, target, wire, accum)) {
            double Redge = wire->r * n->wire_right;
            *accum += Redge * n->right->subtree_c;
            return 1;
        }
    }
    return 0;
}

/* find all leaves in pre-order and perform action via callback */
typedef void (*leaf_cb)(Node *leaf, void *ctx);
static void preorder_leaves(Node *n, leaf_cb cb, void *ctx) {
    if (!n) return;
    if (n->is_leaf) {
        cb(n, ctx);
        return;
    }
    /* internal: visit node (no-op for leaves), then left then right */
    if (n->left) preorder_leaves(n->left, cb, ctx);
    if (n->right) preorder_leaves(n->right, cb, ctx);
}

/* write pre-order topology to text file */
/* Write pre-order topology: matches output #1 format (Step 5).
 * Internal nodes: "(lenLeft lenRight)"; Leaf: "label(cap)" per line.
 */
static void write_preorder_topology(FILE *f, Node *n) {
    if (!n) return;
    if (n->is_leaf) {
        fprintf(f, "%d(%.10le)\n", n->label, n->cap);
        return;
    }
    fprintf(f, "(%.10le %.10le)\n", n->wire_left, n->wire_right);
    write_preorder_topology(f, n->left);
    write_preorder_topology(f, n->right);
}

/* create empty file (truncate) */
/* removed unused helper create_empty_file to reduce dead code */

/* context for leaf writer */
struct cb_ctx { FILE *fel; Node *root; const Wire *wire; double Rb; /* inverter driver Cout to include in leaf delays */ double inv_Cout; Node **all_nodes; size_t all_count; };

/* helper: compute LCA by walking ancestors of a and marking in an array
 * We implement a simple path-based LCA without extra memory by building
 * the ancestor list of a and then walking up from b.
 */
static Node *lca(Node *a, Node *b) {
    if (!a || !b) return NULL;
    /* build ancestor list for a */
    Node *cur = a;
    size_t cap = 64;
    size_t sz = 0;
    Node **anc = malloc(cap * sizeof(Node*));
    while (cur) {
        if (sz == cap) { cap *= 2; anc = realloc(anc, cap * sizeof(Node*)); }
        if (!anc) { fprintf(stderr, "memory allocation failure\n"); return NULL; }
        anc[sz++] = cur;
        cur = cur->parent;
    }
    /* walk up from b and return first node that appears in anc */
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

static void leaf_writer(Node *leaf, void *vctx) {
    struct cb_ctx *c = (struct cb_ctx*)vctx;
    double delay = 0.0;
    /* First-formula: sum over all nodes i of c'_i * Rcommon(i, leaf)
     * where Rcommon(i,leaf) = Rroot(LCA(i,leaf)).
     */
    for (size_t k = 0; k < c->all_count; ++k) {
        Node *i = c->all_nodes[k];
        double ci = i->cprime;
        if (ci == 0.0) continue;
        Node *L = lca(i, leaf);
        if (!L) continue;
        delay += ci * L->Rroot;
    }
    /* include driver's output capacitance at the root as an extra c' term
     * multiplied by Rroot(root). Treat the driver as having at least one
     * stage (implicit) when computing effective Cout for the pre-output.
     */
    double root_k = (double)(c->root->num_inverters ? c->root->num_inverters : 1);
    double Cout_eff = c->inv_Cout * root_k;
    delay += Cout_eff * c->root->Rroot;
    /* write label (int) then double */
    fwrite(&leaf->label, sizeof(int), 1, c->fel);
    fwrite(&delay, sizeof(double), 1, c->fel);
}

/* collect nodes in pre-order into dynamic array *allp; *cntp and *allocp are updated */
static void collect_nodes_pre(Node ***allp, size_t *cntp, size_t *allocp, Node *n) {
    if (!n) return;
    if (*cntp == *allocp) {
        *allocp = (*allocp == 0) ? 64 : (*allocp * 2);
        Node **tmp = realloc(*allp, (*allocp) * sizeof(Node*));
        if (!tmp) { fprintf(stderr, "memory allocation failure\n"); exit(EXIT_FAILURE); }
        *allp = tmp;
    }
    (*allp)[(*cntp)++] = n;
    collect_nodes_pre(allp, cntp, allocp, n->left);
    collect_nodes_pre(allp, cntp, allocp, n->right);
}

/* set Rroot for node and all descendants (Rroot at root should be set before calling) */
static void set_Rroot_recursive(Node *n, const Wire *wire) {
    if (!n) return;
    if (n->left) {
        n->left->Rroot = n->Rroot + wire->r * n->wire_left;
        set_Rroot_recursive(n->left, wire);
    }
    if (n->right) {
        n->right->Rroot = n->Rroot + wire->r * n->wire_right;
        set_Rroot_recursive(n->right, wire);
    }
}

/* find first child of ancestor "from" on the path to node "to" */
static Node *first_child_on_path(Node *from, Node *to) {
    /* walk up from 'to' to find the node whose parent is 'from' */
    Node *p = to;
    Node *prev = NULL;
    while (p && p != from) { prev = p; p = p->parent; }
    if (p == from) return prev; /* prev is immediate child of from on path */
    return NULL;
}

/* Compute Elmore delays from driver node "drv_node" to every leaf in its subtree.
 * Returns max delay and sets worst_leaf_out. Uses inv params and wire.
 */
static double elmore_from_driver(Node *drv_node, const Wire *wire, const Inverter *inv, Node **worst_leaf_out) {
    double max_delay = -1.0;
    Node *worst = NULL;
    /* determine effective Rb and Cout at this driver based on num_inverters */
    int k = drv_node->num_inverters > 0 ? drv_node->num_inverters : 1; /* at least 1 when used as driver */
    double Rb_eff = inv->Rb / (double)k;
    double Cout_eff = inv->Cout * (double)k;

    /* driver_total_cap is drv_node->subtree_c plus driver output cap */
    double driver_total_c = drv_node->subtree_c + Cout_eff;

    /* For each leaf in subtree, compute delay = Rb_eff * driver_total_c + sum_edges Redge * subtree_c(child)
     * We'll traverse subtree and collect leaves.
     */
    /* simple stack traversal */
    Node **stack = NULL; size_t sz = 0, cap = 0;
    /* push drv_node */
    cap = 16; stack = malloc(cap * sizeof(Node*)); stack[sz++] = drv_node;
    if (!stack) { fprintf(stderr, "memory allocation failure\n"); return -1.0; }
    while (sz) {
        Node *n = stack[--sz];
        if (n->is_leaf) {
            double delay = Rb_eff * driver_total_c;
            /* add edge contributions along path from drv_node to this leaf */
            add_path_contributions(drv_node, n, wire, &delay);
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

/* Greedy inverter insertion top-down: insert inverter at offending child of driver until all stage delays <= constraint.
 * This places inverters at existing internal nodes (no wire splitting). It increments num_inverters at a node when inserting.
 */
static void greedy_insert_inverters(Node *root, const Wire *wire, const Inverter *inv, double constraint) {
    /* ensure root has one implicit driver */
    if (root->num_inverters == 0) root->num_inverters = 1;

    /* driver worklist: simple dynamic array of nodes to check */
    Node **drivers = NULL; size_t dcnt = 0, dcap = 0;
    if (dcnt == dcap) { dcap = dcap ? dcap*2 : 16; Node **tmp = realloc(drivers, dcap * sizeof(Node*)); if (!tmp) { fprintf(stderr, "memory allocation failure\n"); return; } drivers = tmp; }
    drivers[dcnt++] = root;

    for (size_t di = 0; di < dcnt; ++di) {
        Node *drv = drivers[di];
        Node *worst = NULL;
        double maxd = elmore_from_driver(drv, wire, inv, &worst);
        if (maxd <= constraint) continue;
        /* find child of drv on path to worst leaf */
        Node *child = first_child_on_path(drv, worst);
        if (!child) continue; /* shouldn't happen */
        /* insert one inverter at child (increase parallel count) */
        child->num_inverters += 1;
        /* add child as a driver to be processed */
    if (dcnt == dcap) { dcap = dcap ? dcap*2 : 16; Node **tmp = realloc(drivers, dcap * sizeof(Node*)); if (!tmp) { free(drivers); fprintf(stderr, "memory allocation failure\n"); return; } drivers = tmp; }
    drivers[dcnt++] = child;
        /* continue loop; the newly added driver will be processed later */
    }
    free(drivers);
}

/* Ensure every leaf is non-inverting: total number of inverters along path (including root implicit) must be even.
 * Root counts as 1 stage (implicit driver). So we require (1 + sum(num_inverters on path)) % 2 == 0 => sum %2 == 1.
 * If a leaf path has wrong parity, insert one inverter at its parent.
 */
static void parity_fix(Node *root) {
    /* traverse all leaves */
    if (!root) return;
    /* collect leaves by traversal */
    Node **stack = NULL; size_t sz = 0, cap = 0;
    cap = 32; stack = malloc(cap * sizeof(Node*));
    if (!stack) { fprintf(stderr, "memory allocation failure\n"); return; }
    stack[sz++] = root;
    while (sz) {
        Node *n = stack[--sz];
        if (n->is_leaf) {
            /* compute sum num_inverters along path from root (excluding root?) include root->num_inverters? We consider root implicit 1 and num_inverters recorded there as well. We define total_inverters = sum over nodes on path of num_inverters; currently root.num_inverters includes implicit driver (1). */
            int sum = 0;
            Node *p = n;
            while (p) { sum += p->num_inverters; p = p->parent; }
            /* total number of inverters along path is sum; we need total to be even -> sum %2 == 0 */
            if ((sum % 2) != 0) {
                /* sum is odd -> total inverters odd -> leaf would be inverting. We need even -> insert one inverter at parent of leaf */
                Node *par = n->parent;
                if (par) par->num_inverters += 1;
                else n->num_inverters += 1; /* if leaf is root (degenerate), insert here */
            }
            continue;
        }
        if (n->right) {
            if (sz == cap) {
                cap *= 2;
                Node **tmp = realloc(stack, cap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return; }
                stack = tmp;
            }
            stack[sz++] = n->right;
        }
        if (n->left) {
            if (sz == cap) {
                cap *= 2;
                Node **tmp = realloc(stack, cap * sizeof(Node*));
                if (!tmp) { free(stack); fprintf(stderr, "memory allocation failure\n"); return; }
                stack = tmp;
            }
            stack[sz++] = n->left;
        }
    }
    free(stack);
}

/* post-order print topology with inverter counts: internal nodes printed as (lenL lenR k)
 * Leaves printed as label(cap). This matches output #3 format.
 */
static void write_postorder_topology(FILE *f, Node *n) {
    if (!n) return;
    if (n->is_leaf) {
        fprintf(f, "%d(%.10le)\n", n->label, n->cap);
        return;
    }
    write_postorder_topology(f, n->left);
    write_postorder_topology(f, n->right);
    /* print node with its inverter count */
    fprintf(f, "(%.10le %.10le %d)\n", n->wire_left, n->wire_right, n->num_inverters);
}

/* binary post-order topology writer: leaf => int label, double cap; internal => int -1, double lenL, double lenR, int k */
static void write_postorder_topology_binary(FILE *f, Node *n) {
    if (!n) return;
    if (n->is_leaf) {
        int lab = n->label;
        fwrite(&lab, sizeof(int), 1, f);
        fwrite(&n->cap, sizeof(double), 1, f);
        return;
    }
    write_postorder_topology_binary(f, n->left);
    write_postorder_topology_binary(f, n->right);
    int marker = -1;
    fwrite(&marker, sizeof(int), 1, f);
    fwrite(&n->wire_left, sizeof(double), 1, f);
    fwrite(&n->wire_right, sizeof(double), 1, f);
    fwrite(&n->num_inverters, sizeof(int), 1, f);
}


int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "Usage: %s time_constraint inv.param wire.param tree.post in.pre out.elmore out.ttopo out.btopo\n", argv[0]);
        return EXIT_FAILURE;
    }

    double time_constraint = atof(argv[1]); (void)time_constraint; /* unused in this minimal solution */

    const char *inv_param = argv[2];
    const char *wire_param = argv[3];
    const char *tree_in = argv[4];
    const char *pre_out = argv[5];
    const char *elmore_out = argv[6];
    const char *ttopo_out = argv[7];
    const char *btopo_out = argv[8];

    /* read inverter params */
    double Cin=0.0, Cout=0.0, Rb=0.0;
    FILE *f = fopen(inv_param, "r");
    if (!f) { perror("inv.param"); return EXIT_FAILURE; }
    if (fscanf(f, "%le %le %le", &Cin, &Cout, &Rb) != 3) { fclose(f); fprintf(stderr, "bad inv.param\n"); return EXIT_FAILURE; }
    fclose(f);

    /* read wire params */
    double r_per_len=0.0, c_per_len=0.0;
    f = fopen(wire_param, "r");
    if (!f) { perror("wire.param"); return EXIT_FAILURE; }
    if (fscanf(f, "%le %le", &r_per_len, &c_per_len) != 2) { fclose(f); fprintf(stderr, "bad wire.param\n"); return EXIT_FAILURE; }
    fclose(f);

    /* read post-order tree and build via stack */
    FILE *tin = fopen(tree_in, "r");
    if (!tin) { perror("tree input"); return EXIT_FAILURE; }

    Node **stack = NULL;
    size_t stack_sz = 0;
    size_t stack_cap = 0;
    char line[512];
    while (fgets(line, sizeof(line), tin)) {
        /* strip leading spaces */
        char *s = line;
        while (*s==' '||*s=='\t' || *s=='\r' || *s=='\n') s++;
        if (*s=='\0') continue;
        /* detect leaf: starts with digit */
        if ((s[0] >= '0' && s[0] <= '9') || s[0]=='-') {
            int label = 0; double cap = 0.0;
            if (sscanf(s, "%d(%lf)", &label, &cap) == 2) {
                Node *n = make_leaf(label, cap);
                if (!n) { fclose(tin); return EXIT_FAILURE; }
                if (stack_sz == stack_cap) { stack_cap = stack_cap ? stack_cap*2 : 16; stack = realloc(stack, stack_cap * sizeof(Node*)); }
                stack[stack_sz++] = n;
                continue;
            }
        }
        /* otherwise expect internal node like: (%.10le %.10le) */
        double l=0.0, r=0.0;
        if (sscanf(s, "(%lf %lf)", &l, &r) == 2) {
            /* pop right then left (post-order) */
            if (stack_sz < 2) { fprintf(stderr, "malformed tree file: not enough children\n"); fclose(tin); return EXIT_FAILURE; }
            Node *right = stack[--stack_sz];
            Node *left = stack[--stack_sz];
            Node *n = make_internal(left, right, l, r);
            if (!n) { fclose(tin); return EXIT_FAILURE; }
            if (stack_sz == stack_cap) { stack_cap = stack_cap ? stack_cap*2 : 16; stack = realloc(stack, stack_cap * sizeof(Node*)); }
            stack[stack_sz++] = n;
            continue;
        }
        /* try alternative formats: sometimes there is an int with parentheses with label starting with space */
        if (sscanf(s, "%d ( %lf )", (int[]){0}, &l) == 0) {
            /* ignore */
        }
    }
    fclose(tin);

    if (stack_sz != 1) {
        fprintf(stderr, "unexpected stack size after parsing: %zu\n", stack_sz);
        for (size_t i=0;i<stack_sz;i++) free_tree(stack[i]);
        free(stack);
        return EXIT_FAILURE;
    }
    Node *root = stack[0];
    free(stack);

    /* compute cprimes and subtree sums */
    Wire wire;
    wire.r = r_per_len;
    wire.c = c_per_len;
    Inverter inv;
    inv.Cin = Cin;
    inv.Cout = Cout;
    inv.Rb = Rb;
    compute_cprimes(root, &wire, &inv);

    /* compute Elmore delays for leaves (pre-order requirement) */
    /* prepare pre-order topology file */
    FILE *fpre = fopen(pre_out, "w");
    if (!fpre) { perror("pre_out"); free_tree(root); return EXIT_FAILURE; }
    write_preorder_topology(fpre, root);
    fclose(fpre);

    /* write binary elmore file (pre-order leaf order) */
    FILE *fel = fopen(elmore_out, "wb");
    if (!fel) { perror("elmore_out"); free_tree(root); return EXIT_FAILURE; }

    /* Prepare nodes array and compute Rroot for each node (resistance from source to node).
     * Rroot at root should include driver Rb. We compute Rroot in a pre-order traversal.
     */
    /* collect nodes into a dynamic array (pre-order) using helper */
    size_t alloc = 0, cnt = 0;
    Node **all = NULL;
    collect_nodes_pre(&all, &cnt, &alloc, root);

    /* compute Rroot: resistance from source to node. Start from root (Rb included)
     * and propagate down adding edge resistances.
     */
    root->Rroot = Rb; /* source -> root includes driver Rb */
    /* set Rroot for all nodes starting at root (root->Rroot set below) */
    set_Rroot_recursive(root, &wire);

    struct cb_ctx ctx;
    ctx.fel = fel; ctx.root = root; ctx.wire = &wire; ctx.Rb = Rb; ctx.inv_Cout = inv.Cout; ctx.all_nodes = all; ctx.all_count = cnt;
    preorder_leaves(root, leaf_writer, &ctx);
    free(all);
    fclose(fel);

    /* Now perform inverter insertion (greedy) using the time constraint */
    greedy_insert_inverters(root, &wire, &inv, time_constraint);
    parity_fix(root);

    /* Write post-order topology text and binary files */
    FILE *ftt = fopen(ttopo_out, "w");
    FILE *fbt = fopen(btopo_out, "wb");
    if (!ftt || !fbt) {
        if (ftt) fclose(ftt);
        if (fbt) fclose(fbt);
        /* leave them empty if we couldn't open */
        free_tree(root);
        return EXIT_FAILURE;
    }
    write_postorder_topology(ftt, root);
    write_postorder_topology_binary(fbt, root);
    fclose(ftt); fclose(fbt);

    free_tree(root);
    return EXIT_SUCCESS;
}
