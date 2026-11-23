/*
 *  busca_sA.c  --  exhaustive search for the numbers mu_m(G) of Section 9 of
 *
 *      A. Lemos, V. G. L. Neumann,
 *      "Rank, exponent and the weighted Gao identity for finite abelian p-groups".
 *
 *  G = Z_{m_1} + ... + Z_{m_r} is a finite abelian p-group with |G| <= 256, n = exp(G),
 *  and A is the set of units of Z_n.  For an integer m with 2 <= m <= 32 and a zero-free
 *  sequence T over G, L_m(T) is the largest l in [1, m-1] such that T has an A-weighted
 *  zero-sum subsequence of length l (L_m(T) = 0 if there is none), and
 *
 *      mu_m(G) = max ( |T| - L_m(T) ),
 *
 *  T running over the zero-free sequences without A-weighted zero-sum subsequence of
 *  length m.  The largest length of a sequence over G without A-weighted zero-sum
 *  subsequence of length m is m - 1 + mu_m(G); in particular s_A(G) = n + mu_n(G).
 *
 *  Method.  All properties depend only on the A-orbits of the terms.  Multisets of orbit
 *  representatives are enumerated in nondecreasing order by depth-first search.  For each
 *  k < m we keep the set Sigma_k of A-weighted sums of the k-term subsequences (a bitset
 *  over G).  These sets are invariant under A, so appending x creates a zero-sum of length
 *  k+1 if and only if x lies in Sigma_k.  A branch is cut when a zero-sum of length m
 *  appears.  The program decides the existence of zero-sums from the definition only.
 *
 *  Compile:   cc -O2 -o busca_sA busca_sA-19-11-26.c
 *
 *  Usage:     ./busca_sA p m mode r m_1 ... m_r [a_1 ... a_r [b_1 ... b_r]] [SPLIT k t] [RESTR i j]
 *
 *     m      length of the forbidden zero-sums (m = 0 means m = exp(G))
 *     mode   0: all zero-free sequences
 *            1: only the sequences which contain a term of the orbit of a
 *            2: only the sequences which contain terms of the orbits of a and of b
 *            3: only the sequences whose first term is a and whose second term (if any)
 *               lies in the orbit of a or is b
 *     SPLIT k t   (optional) only the branches whose third term has index = k mod t;
 *                 the runs k = 0, ..., t-1 together cover the whole search
 *                 (the sequences with at most two terms are visited in every run)
 *     RESTR i j   (optional, for tests) only the elements whose coordinates i and j are
 *                 congruent modulo p (a subgroup, if m_i, m_j are as in the tests below)
 *
 *  Runs quoted in the paper (output: number of sequences visited, mu_m, number of
 *  sequences attaining mu_m and how many of these have L_m = 0):
 *
 *     ./busca_sA 3 0 0 2 3 3            Z_3^2          mu_3 = 2
 *     ./busca_sA 5 0 0 2 5 5            Z_5^2          mu_5 = 2
 *     ./busca_sA 7 0 0 2 7 7            Z_7^2          mu_7 = 2
 *     ./busca_sA 5 0 0 3 5 5 5          Z_5^3          mu_5 = 3
 *     ./busca_sA 3 0 0 2 9 3            Z_9+Z_3        mu_9 = 3
 *     ./busca_sA 3 0 0 2 9 9            Z_9^2          mu_9 = 4
 *     ./busca_sA 3 0 0 3 3 3 3          Z_3^3          mu_3 = 6
 *     ./busca_sA 3 0 0 3 9 3 3          Z_9+Z_3^2      mu_9 = 4
 *     ./busca_sA 3 9 0 3 3 3 3          Z_3^3          mu_9 = 3
 *     ./busca_sA 3 7 0 3 3 3 3          Z_3^3          mu_7 = 3
 *     ./busca_sA 3 9 3 4 3 3 3 3  0 0 0 1  0 0 1 0          Z_3^4, mode 3: 4
 *     ./busca_sA 3 9 1 3 9 9 3  1 0 0                       Z_9^2+Z_3, mode 1: 5
 *     ./busca_sA 3 9 2 4 9 3 3 3  1 0 0 0  1 1 0 0          Z_9+Z_3^3, mode 2: 5
 *
 *  Tests of the program on groups of order larger than 128:
 *     ./busca_sA 13 0 0 2 13 13                    (s_A(Z_13^2) = 15)
 *     ./busca_sA 3 9 0 4 3 9 3 3 RESTR 0 1         (same counts as Z_9+Z_3^2)
 *     ./busca_sA 3 9 0 4 9 3 3 3 RESTR 3 0         (same counts as Z_9+Z_3^2)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { uint64_t w[4]; } mask_t;          /* a subset of G, |G| <= 256 */

#define MAXN 256
#define MAXL 32

static int r, mods[8], N, n, p, LEN, MODE, SK = 0, SM = 1, RI = -1, RJ = -1;
static int orb[MAXN][MAXN], orbsz[MAXN], reps[MAXN], nreps, NB;
static mask_t (*TR)[32][256];                      /* TR[y][byte][value]: translation by y */
static int trans[MAXN][MAXN];
static long long nodes = 0, cnt_max = 0, cnt_max_L0 = 0;
static int best = -1;

static void dec(int i, int *e) { for (int k = r - 1; k >= 0; k--) { e[k] = i % mods[k]; i /= mods[k]; } }
static int enc(const int *e) { int i = 0; for (int k = 0; k < r; k++) i = i * mods[k] + e[k]; return i; }
static inline int tst(const mask_t *S, int i) { return (S->w[i >> 6] >> (i & 63)) & 1; }
static inline int nonempty(const mask_t *S) { return (S->w[0] | S->w[1] | S->w[2] | S->w[3]) != 0; }

/* acc |= S + y */
static inline void or_translate(mask_t *acc, const mask_t *S, int y)
{
    const unsigned char *b = (const unsigned char *)S->w;      /* little-endian byte view */
    for (int k = 0; k < NB; k++) {
        unsigned v = b[k];
        if (v) {
            const mask_t *t = &TR[y][k][v];
            acc->w[0] |= t->w[0]; acc->w[1] |= t->w[1]; acc->w[2] |= t->w[2]; acc->w[3] |= t->w[3];
        }
    }
}

/* Sig[k] = Sigma_k of the current sequence (k = 0..LEN-1); bit k of "has" = there is a
   zero-sum subsequence of length k; hasb = the current sequence contains the orbit of b */
static void rec(int start, int len, const mask_t *Sig, unsigned has, int hasb)
{
    nodes++;
    int ok = 1;
    if (MODE == 1 && len == 0) ok = 0;
    if (MODE == 2 && !hasb) ok = 0;
    if (ok) {
        int L = 0;
        for (int k = LEN - 1; k >= 1; k--) if (has >> k & 1u) { L = k; break; }
        int val = len - L;
        if (val > best) { best = val; cnt_max = 0; cnt_max_L0 = 0; }
        if (val == best) { cnt_max++; if (L == 0) cnt_max_L0++; }
    }
    mask_t NS[MAXL];
    for (int j = start; j < nreps; j++) {
        if (MODE == 1 && len == 0 && j != 0) break;
        if (MODE == 2) { if (len == 0 && j != 0) break; if (len >= 1 && !hasb && j > 1) break; }
        if (MODE == 3) { if (len == 0 && j != 0) break; if (len == 1 && j > 1) break; }
        if (len == 2 && (j % SM) != SK) continue;
        int x = reps[j];
        if (tst(&Sig[LEN - 1], x)) continue;                    /* zero-sum of length LEN */
        unsigned nh = has;
        NS[0] = Sig[0];
        for (int k = 0; k < LEN - 1; k++) {
            if (tst(&Sig[k], x)) nh |= 1u << (k + 1);
            mask_t acc = Sig[k + 1];
            if (nonempty(&Sig[k])) for (int t = 0; t < orbsz[x]; t++) or_translate(&acc, &Sig[k], orb[x][t]);
            NS[k + 1] = acc;
        }
        rec(j, len + 1, NS, nh, hasb || (j == 1));
    }
}

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "usage: %s p m mode r m_1 ... m_r [a_1 ... a_r [b_1 ... b_r]] [SPLIT k t] [RESTR i j]\n", argv[0]);
        return 1;
    }
    p = atoi(argv[1]); LEN = atoi(argv[2]); MODE = atoi(argv[3]); r = atoi(argv[4]);
    if (r < 1 || r > 8 || argc < 5 + r) { fprintf(stderr, "bad arguments\n"); return 1; }
    N = 1; n = 1;
    int pos = 5;
    for (int k = 0; k < r; k++) { mods[k] = atoi(argv[pos++]); N *= mods[k]; if (mods[k] > n) n = mods[k]; }
    if (LEN == 0) LEN = n;
    if (N > MAXN || LEN > MAXL || LEN < 2) { fprintf(stderr, "group too large or bad length\n"); return 1; }
    int ea[8], eb[8], ia = -1, ib = -1;
    if (MODE >= 1) {
        if (argc < pos + r) { fprintf(stderr, "missing a\n"); return 1; }
        for (int k = 0; k < r; k++) ea[k] = atoi(argv[pos++]);
        ia = enc(ea);
    }
    if (MODE >= 2) {
        if (argc < pos + r) { fprintf(stderr, "missing b\n"); return 1; }
        for (int k = 0; k < r; k++) eb[k] = atoi(argv[pos++]);
        ib = enc(eb);
    }
    if (pos + 2 < argc && strcmp(argv[pos], "SPLIT") == 0) { SK = atoi(argv[pos + 1]); SM = atoi(argv[pos + 2]); pos += 3; }
    if (pos + 2 < argc && strcmp(argv[pos], "RESTR") == 0) { RI = atoi(argv[pos + 1]); RJ = atoi(argv[pos + 2]); pos += 3; }

    NB = (N + 7) / 8;
    TR = malloc(sizeof(*TR) * N);
    if (!TR) { fprintf(stderr, "out of memory\n"); return 1; }
    int e[8], f[8], g[8];
    for (int i = 0; i < N; i++) {
        dec(i, e);
        for (int y = 0; y < N; y++) { dec(y, f); for (int k = 0; k < r; k++) g[k] = (e[k] + f[k]) % mods[k]; trans[y][i] = enc(g); }
    }
    for (int y = 0; y < N; y++) for (int b = 0; b < NB; b++) for (int v = 0; v < 256; v++) {
        mask_t R; memset(&R, 0, sizeof(R));
        for (int j = 0; j < 8; j++) if (v >> j & 1) { int i = 8 * b + j; if (i < N) { int t = trans[y][i]; R.w[t >> 6] |= (uint64_t)1 << (t & 63); } }
        TR[y][b][v] = R;
    }
    /* orbits of the units, and one representative (the smallest index) of each nonzero orbit */
    nreps = 0;
    int omega = 0, repof[MAXN];
    for (int k = 0; k < r; k++) { int m = mods[k]; while (m > 1) { m /= p; omega++; } }
    for (int i = 0; i < N; i++) {
        dec(i, e); orbsz[i] = 0; int mn = i;
        for (int a = 1; a <= n; a++) {
            if (a % p == 0) continue;
            for (int k = 0; k < r; k++) g[k] = (a * e[k]) % mods[k];
            int j = enc(g), seen = 0;
            for (int t = 0; t < orbsz[i]; t++) if (orb[i][t] == j) seen = 1;
            if (!seen) orb[i][orbsz[i]++] = j;
            if (j < mn) mn = j;
        }
        repof[i] = mn;
        if (mn == i && i != 0 && (RI < 0 || (e[RI] - e[RJ]) % p == 0)) reps[nreps++] = i;
    }
    /* the orbit of a gets index 0 and the orbit of b gets index 1 */
    if (ia >= 0) {
        int ra = repof[ia], q = -1;
        for (int t = 0; t < nreps; t++) if (reps[t] == ra) q = t;
        if (q < 0) { fprintf(stderr, "bad a\n"); return 1; }
        for (int t = q; t > 0; t--) reps[t] = reps[t - 1];
        reps[0] = ra;
    }
    if (ib >= 0) {
        int rb = repof[ib], q = -1;
        for (int t = 0; t < nreps; t++) if (reps[t] == rb) q = t;
        if (q < 1) { fprintf(stderr, "bad b (same orbit as a?)\n"); return 1; }
        for (int t = q; t > 1; t--) reps[t] = reps[t - 1];
        reps[1] = rb;
    }
    mask_t Sig0[MAXL]; memset(Sig0, 0, sizeof(Sig0)); Sig0[0].w[0] = 1;       /* Sigma_0 = {0} */
    rec(0, 0, Sig0, 0u, 0);

    printf("G = ");
    for (int k = 0; k < r; k++) printf("Z_%d%s", mods[k], k < r - 1 ? " + " : "");
    printf(" : mode %d", MODE);
    if (SM > 1) printf(", split %d/%d", SK, SM);
    if (RI >= 0) printf(", restricted to x_%d = x_%d mod p", RI, RJ);
    printf(", nonzero orbits %d, sequences visited %lld, m = %d, max(|T| - L_m(T)) = %d, m + max = %d (exp + Omega = %d); "
           "sequences attaining the maximum: %lld, of which with L_m(T) = 0: %lld\n",
           nreps, nodes, LEN, best, LEN + best, n + omega, cnt_max, cnt_max_L0);
    return 0;
}
