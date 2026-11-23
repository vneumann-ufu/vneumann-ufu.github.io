# -*- coding: utf-8 -*-
# =============================================================================
#  verificacoes_artigo-19-11-26b.sage
#
#  Computations quoted in Section 9 of
#      A. Lemos, V. G. L. Neumann,
#      "Rank, exponent and the weighted Gao identity for finite abelian p-groups"
#  (version 19-11-26b).
#
#  How to run:
#      sage verificacoes_artigo-19-11-26b.sage          quick  (a few minutes)
#      sage verificacoes_artigo-19-11-26b.sage medium   adds the searches for Z_9 + Z_3^2 and
#                                                       Z_3^4 and the chain test for
#                                                       Z_9 + Z_3^3, Z_16 + Z_2^3 and
#                                                       Z_8 + Z_4 + Z_2^2 (about half an hour)
#      sage verificacoes_artigo-19-11-26b.sage long     adds the two large searches of
#                                                       Proposition 9.1 and the chain test
#                                                       for Z_4^3 + Z_2 (several hours; the C
#                                                       program busca_sA does the two large
#                                                       searches in about ten and eight minutes)
#  Inside a Sage session:   load("verificacoes_artigo-19-11-26b.sage")   and then, e.g.,
#      search(3, 9, 0, [9, 3])        # mu_9(Z_9 + Z_3)
#
#  The code uses only Python integers, lists, sets and dictionaries (no special Sage
#  structure), so that every step can be read and checked.  Whether a sequence has an
#  A-weighted zero-sum subsequence is always decided from the definition (through the
#  sets of all weighted sums); no result of the paper is used for that.
#
#  Notation:  G = Z_{m_1} + ... + Z_{m_r} (a p-group), n = exp(G),
#             A = units of Z_n (integers in [1,n] prime to p).
# =============================================================================

import itertools
import sys
import time


# -----------------------------------------------------------------------------
#  The group G, the orbits of A, subgroups
# -----------------------------------------------------------------------------
class Group(object):
    def __init__(self, p, mods):
        p = int(p)
        self.p = p
        self.mods = [int(m) for m in mods]
        self.r = len(self.mods)
        self.n = max(self.mods)
        self.Omega = 0
        for m in self.mods:
            while m > 1:
                m //= p
                self.Omega += 1
        # element number i <-> tuple elems[i]; the first coordinate is the most significant
        self.elems = [tuple(t) for t in itertools.product(*[range(m) for m in self.mods])]
        self.N = len(self.elems)
        self.idx = dict((e, i) for i, e in enumerate(self.elems))
        self.zero = 0
        self.units = [a for a in range(1, self.n + 1) if a % p != 0]
        self.ADD = [[self.idx[self.add(e, f)] for f in self.elems] for e in self.elems]
        self.orbit = []
        for e in self.elems:
            self.orbit.append(sorted(set(self.idx[self.mul(a, e)] for a in self.units)))
        self.reps = sorted(set(o[0] for o in self.orbit if o[0] != 0))    # nonzero orbits
        self._sub_id = {}
        self._subs = []
        self._join = {}
        self.triv = self._id_sub(frozenset([0]))

    def add(self, e, f):
        return tuple([(e[i] + f[i]) % self.mods[i] for i in range(self.r)])

    def mul(self, a, e):
        return tuple([(a * e[i]) % self.mods[i] for i in range(self.r)])

    def name(self):
        return " + ".join(["Z_%d" % m for m in self.mods])

    def _id_sub(self, H):
        if H not in self._sub_id:
            self._sub_id[H] = len(self._subs)
            self._subs.append(H)
        return self._sub_id[H]

    def join(self, h, x):
        """id of the subgroup <H, x>, where h is the id of H"""
        key = (h, x)
        if key in self._join:
            return self._join[key]
        H = self._subs[h]
        if x in H:
            res = h
        else:
            new = set(H)
            y = x
            while y != 0:
                row = self.ADD[y]
                for s in H:
                    new.add(row[s])
                y = self.ADD[y][x]
            res = self._id_sub(frozenset(new))
        self._join[key] = res
        return res

    def generated(self, seq):
        h = self.triv
        for x in seq:
            h = self.join(h, x)
        return h

    def order_sub(self, h):
        return len(self._subs[h])


# -----------------------------------------------------------------------------
#  (1) The search for mu_m(G)  (Section 9.1 of the paper)
#
#  Sig[k] = set of the A-weighted sums of the k-term subsequences of the current
#  sequence, as a bit mask (bit i <-> element number i).  These sets are invariant
#  under A; hence appending x creates a zero-sum of length k+1  <=>  x in Sig[k].
#
#  mode 0: all zero-free sequences
#  mode 1: the sequences which contain a term of the orbit of a
#  mode 2: the sequences which contain terms of the orbits of a and of b
#  mode 3: first term a; second term (if any) in the orbit of a, or equal to b
# -----------------------------------------------------------------------------
def search(p, m, mode, mods, a=None, b=None, keep=False, verbose=True):
    G = Group(p, mods)
    if m == 0:
        m = G.n
    LEN = int(m)
    mode = int(mode)
    ONE = int(1)                 # Python integers (faster than Sage integers in the loops)
    ZERO = int(0)
    if a is not None:
        a = tuple(int(t) for t in a)
    if b is not None:
        b = tuple(int(t) for t in b)
    N = G.N
    r = G.r
    # translation by y as a composition of "rotations" of the coordinates
    stride = [1] * r
    for k in range(r - 2, -1, -1):
        stride[k] = stride[k + 1] * G.mods[k + 1]
    steps_of = []
    lowmask = {}
    for k in range(r):
        mk = G.mods[k]
        for yk in range(1, mk):
            lo = ZERO
            hi = ZERO
            for i, e in enumerate(G.elems):
                if e[k] + yk < mk:
                    lo |= ONE << i
                else:
                    hi |= ONE << i
            # (S + y_k e_k) = ((S & lo) << ls) | ((S & hi) >> rs)
            lowmask[(k, yk)] = (lo, int(yk * stride[k]), hi, int((mk - yk) * stride[k]))
    for y in range(N):
        e = G.elems[y]
        steps_of.append([lowmask[(k, e[k])] for k in range(r) if e[k] != 0])
    reps = list(G.reps)
    if mode >= 1:
        ra = G.orbit[G.idx[tuple(a)]][0]
        reps.remove(ra)
        reps.insert(0, ra)
    if mode >= 2:
        rb = G.orbit[G.idx[tuple(b)]][0]
        if rb == reps[0]:
            raise ValueError("a and b lie in the same orbit")
        reps.remove(rb)
        reps.insert(1, rb)
    nreps = len(reps)
    orbit_steps = [[steps_of[y] for y in G.orbit[x]] for x in reps]
    bit = [ONE << x for x in reps]
    BIT = [ONE << k for k in range(LEN + 1)]
    stats = {"nodes": ZERO, "best": -1, "count": 0, "countL0": 0, "list": []}

    def rec(start, seq, Sig, has, hasb):
        stats["nodes"] += ONE
        ln = len(seq)
        ok = True
        if mode == 1 and ln == 0:
            ok = False
        if mode == 2 and not hasb:
            ok = False
        if ok:
            L = 0
            for k in range(LEN - 1, 0, -1):
                if (has >> k) & ONE:
                    L = k
                    break
            val = ln - L
            if val > stats["best"]:
                stats["best"] = val
                stats["count"] = 0
                stats["countL0"] = 0
                stats["list"] = []
            if val == stats["best"]:
                stats["count"] += 1
                if L == 0:
                    stats["countL0"] += 1
                if keep:
                    stats["list"].append((tuple(seq), L))
        top = min(LEN - 1, ln + 1)             # Sig[k] is empty for k > ln
        for j in range(start, nreps):
            if mode == 1 and ln == 0 and j != 0:
                break
            if mode == 2:
                if ln == 0 and j != 0:
                    break
                if ln >= 1 and (not hasb) and j > 1:
                    break
            if mode == 3:
                if ln == 0 and j != 0:
                    break
                if ln == 1 and j > 1:
                    break
            bx = bit[j]
            if Sig[LEN - 1] & bx:              # a zero-sum of length LEN would appear
                continue
            nh = has
            new = list(Sig)
            osteps = orbit_steps[j]
            for k in range(top):
                base = Sig[k]
                if base & bx:
                    nh |= BIT[k + 1]
                acc = Sig[k + 1]
                if base:
                    for steps in osteps:
                        s = base
                        for (lo, ls, hi, rs) in steps:
                            s = ((s & lo) << ls) | ((s & hi) >> rs)
                        acc |= s
                new[k + 1] = acc
            rec(j, seq + [reps[j]], new, nh, hasb or (j == 1))

    Sig0 = [ZERO] * LEN
    Sig0[0] = ONE                # Sigma_0 = {0}
    t0 = time.time()
    rec(0, [], Sig0, ZERO, False)
    if verbose:
        print("G = %s : mode %d, nonzero orbits %d, sequences visited %d, m = %d, "
              "max(|T| - L_m(T)) = %d, m + max = %d (exp + Omega = %d); sequences attaining "
              "the maximum: %d, of which with L_m(T) = 0: %d   [%.0f s]"
              % (G.name(), mode, nreps, stats["nodes"], LEN, stats["best"],
                 LEN + stats["best"], G.n + G.Omega, stats["count"], stats["countL0"],
                 time.time() - t0))
        sys.stdout.flush()
    if keep:
        return G, stats
    return stats["nodes"], stats["best"], stats["count"], stats["countL0"]


# -----------------------------------------------------------------------------
#  (2) Zero-sum free sequences and chain sequences  (Theorem 1.4)
#
#  All zero-sum free sequences (multisets of nonzero orbits) are enumerated, and each of
#  them is tested for being a chain sequence (by removing, as long as possible, a term
#  which lies outside the subgroup generated by the other terms).
# -----------------------------------------------------------------------------
def check_chains(p, mods, verbose=True):
    G = Group(p, mods)
    reps = G.reps
    count = {}
    not_chain = {}            # length -> number of zero-sum free sequences which are not chains
    closed = {}               # length -> number of those in which every term lies in the
    example = [None]          #           subgroup generated by the other terms
    longest = [0]

    def outside_index(seq):
        """index of a term outside the subgroup generated by the other terms, or -1"""
        total = G.order_sub(G.generated(seq))
        for i in range(len(seq)):
            if i > 0 and seq[i] == seq[i - 1]:
                continue
            if G.order_sub(G.generated(seq[:i] + seq[i + 1:])) < total:
                return i
        return -1

    def is_chain(seq):
        # a chain sequence has a term b outside the subgroup generated by the others, and
        # removing any such b leaves a chain sequence (subsequences of chains are chains)
        seq = list(seq)
        while seq:
            i = outside_index(seq)
            if i < 0:
                return False
            del seq[i]
        return True

    def rec(start, seq, Sigma):
        l = len(seq)
        count[l] = count.get(l, 0) + 1
        if l > longest[0]:
            longest[0] = l
        if l >= 1:
            i = outside_index(seq)
            if i < 0:
                closed[l] = closed.get(l, 0) + 1
                not_chain[l] = not_chain.get(l, 0) + 1
                if example[0] is None:
                    example[0] = [G.elems[x] for x in seq]
            elif not is_chain(seq[:i] + seq[i + 1:]):
                not_chain[l] = not_chain.get(l, 0) + 1
        for j in range(start, len(reps)):
            x = reps[j]
            if x in Sigma:                 # a zero-sum would appear
                continue
            new = set(Sigma)
            for y in G.orbit[x]:
                new.add(y)
                row = G.ADD[y]
                for s in Sigma:
                    new.add(row[s])
            rec(j, seq + [x], new)

    rec(0, [], set())
    bad = sum(not_chain.values())
    if verbose:
        print("   %-22s rank %d, Omega %d: longest zero-sum free sequence %d; zero-sum free "
              "sequences by length %s; not chain sequences: %d"
              % (G.name(), G.r, G.Omega, longest[0],
                 [count[k] for k in sorted(count) if k >= 1], bad))
        if bad > 0:
            print("      not chain sequences (length: number): %s; among them, sequences in "
                  "which every term lies in the subgroup generated by the others: %s; example: %s"
                  % (sorted(not_chain.items()), sorted(closed.items()), example[0]))
        sys.stdout.flush()
    return longest[0], bad


# -----------------------------------------------------------------------------
#  (3) The sequence of Proposition 4.10:  G = Z_{p^2}^{p+1} + Z_p^{p-1} with basis
#      f_0, ..., f_p (order p^2) and h_1, ..., h_{p-1} (order p),
#         w_j = h_j (1 <= j <= p-1),   w_0 = -(h_1 + ... + h_{p-1}),
#         w_p = -(h_1 + 2 h_2 + ... + (p-1) h_{p-1}),
#         a_t = f_t + w_t + p f_{t+1}      (indices modulo p+1),
#      T = f_0 a_0 f_1 a_1 ... f_p a_p.
#
#  From the definition: let c_t be the weight of a_t (c_t = 0 if a_t is not used).  The
#  terms f_s can complete sum_t c_t a_t to a zero-sum if and only if
#    (i)  every h-coordinate of sum_t c_t a_t vanishes (modulo p), and
#    (ii) every f-coordinate of sum_t c_t a_t (modulo p^2) is 0 (f_s not used) or a unit
#         (f_s used with the opposite weight).
#  So T is zero-sum free  <=>  no (c_0, ..., c_p) != 0 with entries in {0} U A satisfies (i)
#  and (ii).  Condition (i) depends only on the residues of the c_t modulo p; the program
#  runs through all residue vectors, keeps those which satisfy (i) and, for each of them,
#  runs through all the weights with these residues.
#
#  "Every term lies in the subgroup generated by the other terms" is tested through the
#  images in G/pG (Lemma 2.1): the images of the other terms must span G/pG.
# -----------------------------------------------------------------------------
def example_sequence(p):
    p = int(p)
    q = p * p
    r = 2 * p
    mods = [q] * (p + 1) + [p] * (p - 1)
    f = [tuple(1 if i == t else 0 for i in range(r)) for t in range(p + 1)]
    w = [[0] * (p - 1) for t in range(p + 1)]       # h-coordinates of w_0, ..., w_p
    for j in range(1, p):
        w[j][j - 1] = 1
        w[0][j - 1] = (p - 1) % p                   # -1
        w[p][j - 1] = (p - j) % p                   # -j
    a = []
    for t in range(p + 1):
        v = [0] * r
        v[t] = 1
        nxt = (t + 1) % (p + 1)
        v[nxt] = (v[nxt] + p) % q
        for j in range(p - 1):
            v[p + 1 + j] = w[t][j]
        a.append(tuple(v))
    return mods, f, a


def rank_mod_p(rows, p):
    p = int(p)
    M = [[int(x) % p for x in row] for row in rows]
    rk = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = -1
        for i in range(rk, len(M)):
            if M[i][c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(int(M[rk][c]), int(p - 2), int(p)) if p > 2 else 1
        M[rk] = [(x * inv) % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                fac = M[i][c]
                M[i] = [(x - fac * y) % p for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


def check_example(p, brute_force=False):
    p = int(p)
    q = p * p
    mods, f, a = example_sequence(p)
    r = 2 * p
    lifts = dict((res, [c for c in range(1, q) if c % p == res]) for res in range(1, p))
    tested = 0
    found = 0
    for kappa in itertools.product(range(p), repeat=p + 1):
        if not any(kappa):
            continue
        if any(sum(kappa[t] * a[t][p + 1 + j] for t in range(p + 1)) % p != 0 for j in range(p - 1)):
            continue                                  # (i) fails
        choices = [[0] if kappa[t] == 0 else lifts[kappa[t]] for t in range(p + 1)]
        for c in itertools.product(*choices):
            tested += 1
            good = True
            for s in range(p + 1):
                x = sum(c[t] * a[t][s] for t in range(p + 1)) % q
                if x != 0 and x % p == 0:             # neither 0 nor a unit: (ii) fails
                    good = False
                    break
            if good:
                found += 1
    T = []
    for t in range(p + 1):
        T.append(f[t])
        T.append(a[t])
    images = [[x % p for x in y] for y in T]
    closed = (rank_mod_p(images, p) == r and
              all(rank_mod_p(images[:i] + images[i + 1:], p) == r for i in range(len(T))))
    msg = ("   p = %d: weights (c_0,...,c_p) != 0 satisfying (i): %d; among them, those which can be "
           "completed to a zero-sum: %d; every term lies in the subgroup generated by the others: %s"
           % (p, tested, found, closed))
    if brute_force:
        # all choices of weights in {0} U A for the 2p+2 terms (meet in the middle)
        weights = [0] + [c for c in range(1, q) if c % p != 0]
        half = len(T) // 2

        def sums(part):
            tab = {}
            for wt in itertools.product(weights, repeat=len(part)):
                sm = tuple(sum(wt[j] * part[j][i] for j in range(len(part))) % mods[i] for i in range(r))
                tab[sm] = tab.get(sm, 0) + 1
            return tab
        t1 = sums(T[:half])
        t2 = sums(T[half:])
        sol = 0
        for s2 in t2:
            neg = tuple((-s2[i]) % mods[i] for i in range(r))
            if neg in t1:
                sol += t1[neg] * t2[s2]
        msg += "; brute force over all weights: %d nonempty zero-sum subsequences" % (sol - 1)
    print(msg)
    sys.stdout.flush()
    return found


# -----------------------------------------------------------------------------
#  (4) The weights lemma (Lemma 6.1), exhaustively
# -----------------------------------------------------------------------------
def has_good_weights(p, vectors, d):
    for c in itertools.product(range(1, p), repeat=len(vectors)):
        ok = True
        for k in range(d):
            if sum(c[j] * vectors[j][k] for j in range(len(vectors))) % p == 0:
                ok = False
                break
        if ok:
            return True
    return False


def configuration_E(p, vectors, d):
    p = int(p)
    d = int(d)
    if d != p - 1:
        return False
    nz = [v for v in vectors if any(x != 0 for x in v)]
    if len(nz) != 2:
        return False
    u, v = nz
    if any(x == 0 for x in u) or any(x == 0 for x in v):
        return False
    e = int(p - 2)                # u^(p-2) = 1/u in F_p
    quot = set((v[k] * pow(int(u[k]), e, p)) % p for k in range(d))
    return len(quot) == p - 1


def check_weights_lemma(p, d, s):
    p = int(p)
    d = int(d)
    s = int(s)
    vec = [tuple(t) for t in itertools.product(range(p), repeat=d)]
    total = 0
    exceptional = 0
    for fam in itertools.combinations_with_replacement(vec, s):
        if not all(any(v[k] != 0 for v in fam) for k in range(d)):
            continue                      # hypothesis of the lemma not satisfied
        total += 1
        good = has_good_weights(p, fam, d)
        E = configuration_E(p, fam, d)
        if E:
            exceptional += 1
        if good == E:                     # the lemma says: good <=> not (E)
            print("   DISCREPANCY in the weights lemma:", p, d, fam)
            return False
    print("   p = %d, d = %d, s = %d: %d multisets satisfying the hypothesis, %d in the "
          "configuration (E); 'good weights exist' <=> 'not (E)' for all of them"
          % (p, d, s, total, exceptional))
    sys.stdout.flush()
    return True


# -----------------------------------------------------------------------------
#  (5) Minimal zero-sum sequences  (Example 9.2)
# -----------------------------------------------------------------------------
def is_zero_sum(G, seq):
    """is the whole sequence an A-weighted zero-sum sequence?"""
    S = set([0])
    for x in seq:
        T = set()
        for y in G.orbit[x]:
            row = G.ADD[y]
            for s in S:
                T.add(row[s])
        S = T
    return 0 in S


def is_zero_sum_free(G, seq):
    Sigma = set()
    for x in seq:
        if x == 0 or x in Sigma:
            return False
        new = set(Sigma)
        for y in G.orbit[x]:
            new.add(y)
            row = G.ADD[y]
            for s in Sigma:
                new.add(row[s])
        Sigma = new
    return True


def is_minimal_zero_sum(G, seq):
    seq = tuple(seq)
    if not is_zero_sum(G, seq):
        return False
    # a zero-sum sequence is minimal <=> removing any one term leaves a zero-sum free sequence
    return all(is_zero_sum_free(G, seq[:i] + seq[i + 1:]) for i in range(len(seq)))


def count_minimal_zero_sums(p, mods):
    G = Group(p, mods)
    out = [(1, 1)]                        # the sequence consisting of the term 0
    for m in range(2, G.Omega + 2):
        c = 0
        for S in itertools.combinations_with_replacement(G.reps, m):
            if is_minimal_zero_sum(G, S):
                c += 1
        out.append((m, c))
    print("   %s: (length, number of minimal zero-sum sequences up to units): %s" % (G.name(), out))
    sys.stdout.flush()
    return out


def check_minimal_example(p):
    p = int(p)
    G = Group(p, [p * p, p * p])
    seq = [G.orbit[G.idx[t]][0] for t in [(0, 1), (1, 0), (1, p), (p, 1)]]
    print("   (0,1)(1,0)(1,%d)(%d,1) over Z_%d^2 is a minimal zero-sum sequence: %s"
          % (p, p, p * p, is_minimal_zero_sum(G, seq)))
    sys.stdout.flush()


# -----------------------------------------------------------------------------
#  (6) Shape of the sequences attaining mu_m in the elementary cases
# -----------------------------------------------------------------------------
def describe_extremal(p, mods):
    G, st = search(p, 0, 0, mods, keep=True, verbose=False)
    shapes = {}
    for seq, L in st["list"]:
        mult = sorted([seq.count(x) for x in set(seq)])
        key = (L, tuple(mult))
        shapes[key] = shapes.get(key, 0) + 1
    print("   %s: mu = %d; sequences T attaining it, by (L(T), multiplicities of the orbits): %s"
          % (G.name(), st["best"], sorted(shapes.items())))
    sys.stdout.flush()


# =============================================================================
if __name__ == "__main__":
    level = "quick"
    if len(sys.argv) > 1:
        level = str(sys.argv[1])
    if level not in ("quick", "medium", "long"):
        level = "quick"

    print("(1) The numbers mu_m(G);  s_A(G) = exp(G) + mu_exp(G)(G)")
    search(3, 0, 0, [3, 3])
    search(5, 0, 0, [5, 5])
    search(7, 0, 0, [7, 7])
    search(5, 0, 0, [5, 5, 5])
    search(3, 0, 0, [9, 3])
    search(3, 0, 0, [9, 9])
    search(3, 0, 0, [3, 3, 3])
    search(3, 9, 0, [3, 3, 3])
    search(3, 7, 0, [3, 3, 3])
    if level in ("medium", "long"):
        search(3, 0, 0, [9, 3, 3])
        search(3, 9, 3, [3, 3, 3, 3], a=[0, 0, 0, 1], b=[0, 0, 1, 0])
    if level == "long":
        search(3, 9, 1, [9, 9, 3], a=[1, 0, 0])
        search(3, 9, 2, [9, 3, 3, 3], a=[1, 0, 0, 0], b=[1, 1, 0, 0])

    print("(1') Shape of the sequences attaining mu in elementary groups")
    describe_extremal(3, [3, 3])
    describe_extremal(5, [5, 5])
    describe_extremal(7, [7, 7])
    describe_extremal(5, [5, 5, 5])
    describe_extremal(3, [3, 3, 3])

    print("(2) Zero-sum free sequences and chain sequences (Theorem 1.4)")
    print("    groups with rk(G) <= 2p-1:")
    cases = [(3, [9]), (3, [27]), (5, [25]), (3, [3, 3]), (5, [5, 5]), (3, [9, 3]),
             (3, [9, 9]), (3, [27, 3]), (5, [25, 5]), (3, [3, 3, 3]), (5, [5, 5, 5]),
             (3, [9, 3, 3]), (5, [25, 5, 5]), (3, [9, 9, 3]),
             (2, [4, 2]), (2, [4, 4]), (2, [8, 2]), (2, [4, 2, 2]),
             (2, [4, 4, 2]), (2, [4, 4, 4]), (2, [8, 4, 2])]
    if level in ("medium", "long"):
        cases.append((3, [9, 3, 3, 3]))
    for (p, mods) in cases:
        check_chains(p, mods)
    print("    2-groups with rank >= 4 and rk(2G) <= 2:")
    check_chains(2, [4, 2, 2, 2])
    check_chains(2, [8, 2, 2, 2])
    check_chains(2, [4, 4, 2, 2])
    check_chains(2, [4, 2, 2, 2, 2])
    if level in ("medium", "long"):
        check_chains(2, [16, 2, 2, 2])
        check_chains(2, [8, 4, 2, 2])
    if level == "long":
        print("    the group of Proposition 4.10 for p = 2 (rank 4, rk(2G) = 3); "
              "14336 zero-sum free sequences which are not chains are expected:")
        check_chains(2, [4, 4, 4, 2])

    print("(3) The sequence of Proposition 4.10")
    check_example(2, brute_force=True)
    check_example(3, brute_force=True)
    check_example(5)

    print("(4) The weights lemma (Lemma 6.1)")
    for (p, d, s) in [(3, 1, 1), (3, 1, 2), (3, 1, 3), (3, 1, 4), (3, 2, 1), (3, 2, 2),
                      (3, 2, 3), (3, 2, 4), (5, 1, 1), (5, 1, 2), (5, 1, 3), (5, 2, 1),
                      (5, 2, 2), (5, 2, 3), (5, 3, 1), (5, 3, 2), (5, 3, 3), (5, 4, 2)]:
        check_weights_lemma(p, d, s)

    print("(5) Minimal zero-sum sequences (Example 9.2)")
    check_minimal_example(3)
    check_minimal_example(5)
    check_minimal_example(7)
    count_minimal_zero_sums(3, [9, 3])
    count_minimal_zero_sums(3, [9, 9])
    print("done")
