# Rank, exponent and the weighted Gao identity for finite abelian p-groups

Programs and outputs for the computations in Section 9 of the paper

> A. Lemos, V. G. L. Neumann, *Rank, exponent and the weighted Gao identity for finite abelian p-groups*.

Web page of this folder: <https://vneumann-ufu.github.io/repositorio/rank-exponent-weighted-gao-identity/>

## Notation

`G` is a finite abelian p-group, `A` is the set of units modulo `exp(G)`, and `s_A(G)` is the
smallest `t` such that every sequence over `G` of length `t` has an A-weighted zero-sum
subsequence of length `exp(G)`. For an integer `m >= 2`, the searches compute the number
`mu_m(G)` defined in Section 9.1 of the paper: the largest length of a sequence over `G`
without A-weighted zero-sum subsequence of length `m` is `m - 1 + mu_m(G)`. In particular,
`s_A(G) = exp(G) + mu_exp(G)(G)`.

## Files

| File | Contents |
|---|---|
| `busca_sA-19-11-26.c` | C program for the exhaustive searches of Section 9. Its header describes the method, the arguments and the runs quoted in the paper. |
| `saidas_busca_sA-19-11-26.txt` | Outputs of the C program: each command and the line it printed. |
| `verificacoes_artigo-19-11-26b.sage` | SageMath script: a second implementation of the search, and the checks of Section 9.3. |
| `saidas_verificacoes_artigo-19-11-26b.txt` | Outputs of the SageMath script: the level `medium`, and the enumeration over `Z_4^3 + Z_2`, which was run separately. The first lines give the version of Sage that was used. |

## How to run

### The C program

    cc -O2 -o busca_sA busca_sA-19-11-26.c
    ./busca_sA p m mode r m_1 ... m_r [a_1 ... a_r [b_1 ... b_r]]

Here `G = Z_{m_1} + ... + Z_{m_r}` is a p-group with `|G| <= 256`, and `m` is the length of
the forbidden zero-sums (`m = 0` stands for `m = exp(G)`). With `mode = 0` the search runs
through all zero-free sequences without zero-sum subsequence of length `m`, up to units. The
modes 1, 2 and 3 restrict the search to sequences containing terms of prescribed orbits, given
by the elements `a` and `b`; they are described in the header of the program. For example,

    ./busca_sA 3 0 0 3 9 3 3

prints

    G = Z_9 + Z_3 + Z_3 : mode 0, nonzero orbits 22, sequences visited 7745097, m = 9, max(|T| - L_m(T)) = 4, m + max = 13 (exp + Omega = 13); sequences attaining the maximum: 2826, of which with L_m(T) = 0: 2826

that is, `mu_9(Z_9 + Z_3^2) = 4` and `s_A(Z_9 + Z_3^2) = 13`. On one core of an Intel Xeon
processor at 2.1 GHz this search takes a few seconds, and the two large searches of
Proposition 9.1 take about ten and eight minutes.

### The SageMath script

    sage verificacoes_artigo-19-11-26b.sage
    sage verificacoes_artigo-19-11-26b.sage medium
    sage verificacoes_artigo-19-11-26b.sage long

Without argument the script runs the quick checks. The level `medium` adds the searches for
`Z_9 + Z_3^2` and `Z_3^4`, and the enumeration of the zero-sum free sequences over
`Z_9 + Z_3^3`, `Z_16 + Z_2^3` and `Z_8 + Z_4 + Z_2^2`. The level `long` adds the two large
searches of Proposition 9.1 and the enumeration over `Z_4^3 + Z_2`. The script uses only
Python integers, lists, sets and dictionaries, and it decides the existence of zero-sums from
the definition.

On one core of an Intel Xeon processor at 2.1 GHz, the level `medium` takes about 19 minutes,
and the enumeration over `Z_4^3 + Z_2` about 32 minutes.

## Runs of the C program

The file `saidas_busca_sA-19-11-26.txt` contains the following runs. The column "max" is the
maximum of `|T| - L_m(T)` found by the search; with `mode = 0` it is `mu_m(G)`.

| Arguments of `busca_sA` | Group | m | max | Where it is used |
|---|---|---|---|---|
| `3 0 0 2 3 3` | Z_3^2 | 3 | 2 | Table of Section 9.2: s_A = 5 |
| `5 0 0 2 5 5` | Z_5^2 | 5 | 2 | Table of Section 9.2: s_A = 7 |
| `7 0 0 2 7 7` | Z_7^2 | 7 | 2 | Table of Section 9.2: s_A = 9 |
| `5 0 0 3 5 5 5` | Z_5^3 | 5 | 3 | Table of Section 9.2: s_A = 8 |
| `3 0 0 2 9 3` | Z_9 + Z_3 | 9 | 3 | Table of Section 9.2: s_A = 12 |
| `3 0 0 2 9 9` | Z_9^2 | 9 | 4 | Table of Section 9.2: s_A = 13 |
| `3 0 0 3 3 3 3` | Z_3^3 | 3 | 6 | Table of Section 9.2: s_A = 9 |
| `3 0 0 3 9 3 3` | Z_9 + Z_3^2 | 9 | 4 | Proposition 9.1: s_A = 13 |
| `3 9 0 3 3 3 3` | Z_3^3 | 9 | 3 | Proof of Proposition 9.1, the group Z_9^2 + Z_3 (sequences without terms of order 9) |
| `3 7 0 3 3 3 3` | Z_3^3 | 7 | 3 | Proof of Proposition 9.1, case (iii) |
| `3 9 3 4 3 3 3 3  0 0 0 1  0 0 1 0` | Z_3^4 | 9 | 4 | Proof of Proposition 9.1, case (i) |
| `3 9 1 3 9 9 3  1 0 0` | Z_9^2 + Z_3 | 9 | 5 | Proposition 9.1: s_A = 14 |
| `3 9 2 4 9 3 3 3  1 0 0 0  1 1 0 0` | Z_9 + Z_3^3 | 9 | 5 | Proposition 9.1, case (iv): s_A = 14 |
| `13 0 0 2 13 13` | Z_13^2 | 13 | 2 | Test of the program on a group of order 169: s_A = 15 |
| `3 9 0 4 3 9 3 3 RESTR 0 1` and `3 9 0 4 9 3 3 3 RESTR 3 0` | a subgroup isomorphic to Z_9 + Z_3^2 of Z_9 + Z_3^3, in two coordinate orders | 9 | 4 | Tests of the program: same numbers as for Z_9 + Z_3^2 |

For each run the output also gives the number of sequences visited and the number of
sequences attaining the maximum; these are the numbers quoted in the proof of Proposition 9.1
and in Section 9.3.

## Checks of the SageMath script

1. The numbers `mu_m(G)`: the searches of the C program, with the same numbers. The two large
   searches of Proposition 9.1 are run only at the level `long`.
2. The shape of the sequences attaining `mu_p` in Z_3^2, Z_5^2, Z_7^2, Z_5^3 and Z_3^3
   (Section 9.3; part (1') of the output).
3. Theorem 1.4: enumeration of the zero-sum free sequences over the groups listed in
   Section 9.3, and the test of whether each of them is a chain sequence (part (2)).
4. Proposition 4.10: the sequence is zero-sum free, checked from the definition for
   p = 2, 3 and 5 (part (3)).
5. Lemma 6.1, checked exhaustively for the parameters listed in Section 9.3 (part (4)).
6. Example 9.2: the sequence (0,1)(1,0)(1,p)(p,1) over Z_{p^2}^2 is a minimal zero-sum
   sequence, for p = 3, 5 and 7; the numbers of minimal zero-sum sequences over Z_9 + Z_3
   and Z_9^2, by length (part (5)).

## Contact

Victor G. L. Neumann, Universidade Federal de Uberlândia — victor.neumann@ufu.br
