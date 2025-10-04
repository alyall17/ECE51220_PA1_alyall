/*
 * pa1.c
 * Rewritten to follow the student's implementation plan.
 * Features implemented in this file:
 * - Data structures for Node, Inverter, and Wire (Step 1)
 * - Parsing functions for inverter, wire, and post-order tree (Step 2)
 * - RC parameter computations (Step 3)
 * - Elmore delay computation using the second formula (Step 4)
 * - Pre-order / post-order printers and binary writers (Step 5)
 * - A stub for inverter insertion (Step 6) — greedy algorithm to be implemented next
 *
 * This version produces Output #1 (pre-order) and Output #2 (binary elmore).
 * Output #3 and #4 (topology with inverters) remain unimplemented and are
 * left as empty files; in that case the program returns EXIT_FAILURE as
 * permitted by the assignment when no inverter insertion is produced.
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
    /* Under the alternative convention, place the entire edge capacitance
     * Ce = wire->c * length onto the child node. Since children were
     * already processed, we add Ce to their cprime and subtree_c here.
     */
    if (n->left) {
        double Ce_left = wire->c * n->wire_left;
        n->left->cprime += Ce_left;
        n->left->subtree_c += Ce_left;
    }
    if (n->right) {
        double Ce_right = wire->c * n->wire_right;
        n->right->cprime += Ce_right;
        n->right->subtree_c += Ce_right;
    }

    double cp = 0.0;
    if (n->is_leaf) cp += n->cap;
    /* Do NOT lump driver Cout at root in this variant; driver Cout will
     * be accounted for separately in the stage delay if needed.
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
static int create_empty_file(const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f) return -1;
    fclose(f);
    return 0;
}

/* context for leaf writer */
struct cb_ctx { FILE *fel; Node *root; const Wire *wire; double Rb; Node **all_nodes; size_t all_count; };

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
    /* write label (int) then double */
    fwrite(&leaf->label, sizeof(int), 1, c->fel);
    fwrite(&delay, sizeof(double), 1, c->fel);
}

/* collect nodes in pre-order into dynamic array *allp; *cntp and *allocp are updated */
static void collect_nodes_pre(Node ***allp, size_t *cntp, size_t *allocp, Node *n) {
    if (!n) return;
    if (*cntp == *allocp) {
        *allocp = (*allocp == 0) ? 64 : (*allocp * 2);
        *allp = realloc(*allp, (*allocp) * sizeof(Node*));
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
    ctx.fel = fel; ctx.root = root; ctx.wire = &wire; ctx.Rb = Rb; ctx.all_nodes = all; ctx.all_count = cnt;
    preorder_leaves(root, leaf_writer, &ctx);
    free(all);
    fclose(fel);

    /* For this minimal implementation we do not attempt to insert inverters.
     * Create/truncate the requested inverter output files as empty files and
     * return EXIT_FAILURE (per assignment instructions this is acceptable).
     */
    create_empty_file(ttopo_out);
    create_empty_file(btopo_out);

    free_tree(root);
    return EXIT_FAILURE;
}
