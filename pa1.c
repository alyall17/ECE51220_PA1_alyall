/* pa1.c
 * Minimal implementation for ECE51220 PA1.
 * - Parses inverter and wire parameters and a post-order tree file
 * - Builds an in-memory strictly-binary tree
 * - Computes Elmore delays for all leaves and writes:
 *   - pre-order text topology (argv[5])
 *   - binary elmore file (argv[6])
 * - For inverter insertion (argv[7] and argv[8]) this minimal
 *   implementation leaves the files empty and returns EXIT_FAILURE
 *   as permitted by the assignment when a solution is not produced.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef struct Node {
    int is_leaf;
    int label; /* if leaf */
    double sink_cap; /* if leaf */
    /* children */
    struct Node *left, *right, *parent;
    double len_left, len_right; /* wire lengths to children */
    /* computed values */
    double cprime; /* node capacitance including half-edge caps and sink and driver if root */
    double subtree_c; /* sum of cprime in subtree */
} Node;

/* helpers */
static Node *make_leaf(int label, double cap) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->is_leaf = 1;
    n->label = label;
    n->sink_cap = cap;
    return n;
}

static Node *make_internal(Node *left, Node *right, double llen, double rlen) {
    Node *n = calloc(1, sizeof(Node));
    if (!n) return NULL;
    n->is_leaf = 0;
    n->left = left; n->right = right;
    n->len_left = llen; n->len_right = rlen;
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
static void compute_cprimes(Node *n, double c_per_len, double driver_Co) {
    if (!n) return;
    compute_cprimes(n->left, c_per_len, driver_Co);
    compute_cprimes(n->right, c_per_len, driver_Co);
    double cp = 0.0;
    if (n->is_leaf) cp += n->sink_cap;
    if (n->left) cp += (c_per_len * n->len_left) * 0.5; /* half of left-edge capacitance */
    if (n->right) cp += (c_per_len * n->len_right) * 0.5; /* half of right-edge capacitance */
    /* if root, include driver output capacitance */
    if (!n->parent) cp += driver_Co;
    n->cprime = cp;
    n->subtree_c = cp + (n->left ? n->left->subtree_c : 0.0) + (n->right ? n->right->subtree_c : 0.0);
}

/* add edge contributions along path: helper that searches for target leaf and
 * accumulates R_edge * subtree_c(child) when unwinding. Returns 1 if found. */
static int add_path_contributions(Node *n, Node *target, double r_per_len, double *accum) {
    if (!n) return 0;
    if (n == target) return 1;
    if (n->left) {
        if (add_path_contributions(n->left, target, r_per_len, accum)) {
            double Redge = r_per_len * n->len_left;
            *accum += Redge * n->left->subtree_c;
            return 1;
        }
    }
    if (n->right) {
        if (add_path_contributions(n->right, target, r_per_len, accum)) {
            double Redge = r_per_len * n->len_right;
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
static void write_preorder_topology(FILE *f, Node *n) {
    if (!n) return;
    if (n->is_leaf) {
        fprintf(f, "%d(%.10le)\n", n->label, n->sink_cap);
        return;
    }
    fprintf(f, "(%.10le %.10le)\n", n->len_left, n->len_right);
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
struct cb_ctx { FILE *fel; Node *root; double r_per_len; double Rb; double total_root_c; };

static void leaf_writer(Node *leaf, void *vctx) {
    struct cb_ctx *c = (struct cb_ctx*)vctx;
    double delay = 0.0;
    /* driver resistance contribution */
    delay += c->Rb * c->total_root_c;
    /* add edge contributions along path */
    add_path_contributions(c->root, leaf, c->r_per_len, &delay);
    /* write label (int) then double */
    fwrite(&leaf->label, sizeof(int), 1, c->fel);
    fwrite(&delay, sizeof(double), 1, c->fel);
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
    compute_cprimes(root, c_per_len, Cout);

    /* compute Elmore delays for leaves (pre-order requirement) */
    /* prepare pre-order topology file */
    FILE *fpre = fopen(pre_out, "w");
    if (!fpre) { perror("pre_out"); free_tree(root); return EXIT_FAILURE; }
    write_preorder_topology(fpre, root);
    fclose(fpre);

    /* write binary elmore file (pre-order leaf order) */
    FILE *fel = fopen(elmore_out, "wb");
    if (!fel) { perror("elmore_out"); free_tree(root); return EXIT_FAILURE; }

    /* total root subtree sum used with driver Rb */
    double total_root_c = root->subtree_c;
    struct cb_ctx ctx;
    ctx.fel = fel; ctx.root = root; ctx.r_per_len = r_per_len; ctx.Rb = Rb; ctx.total_root_c = total_root_c;
    preorder_leaves(root, leaf_writer, &ctx);
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
