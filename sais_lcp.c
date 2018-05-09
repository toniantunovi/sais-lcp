#include "sais_lcp.h"

unsigned char MASK[] = {0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01};
#define TGET(i) ((t[(i) / 8] & MASK[(i) % 8]) ? 1 : 0)
#define TSET(i, b) t[(i) / 8] = (b) ? (MASK[(i) % 8] | t[(i) / 8]) : ((~MASK[(i) % 8]) & t[(i) / 8])
#define CHR(i) (cs == sizeof(int) ? ((int *)s)[i] : ((unsigned char *)s)[i])
#define IS_LMS(i) (i > 0 && TGET(i) && !TGET(i - 1))

static void get_counts(const void *s, int *counts, int n, int K, int cs)
{
    int i;
    for (i = 0; i <= K; ++i)
    {
        counts[i] = 0;
    }
    for (i = 0; i < n; ++i)
    {
        ++counts[CHR(i)];
    }
}

static void get_buckets(const int *counts, int *bkt, int K, int end)
{
    int i, sum = 0;
    if (end)
    {
        for (i = 0; i <= K; ++i)
        {
            sum += counts[i];
            bkt[i] = sum;
        }
    }
    else
    {
        for (i = 0; i <= K; ++i)
        {
            sum += counts[i];
            bkt[i] = sum - counts[i];
        }
    }
}

void induce_sa(const unsigned char *t, int *SA, const void *s, const int *counts, int *bkt, int n, int K, int cs)
{
    int i, j;

    // Induce L-type.
    // Find starts of buckets.
    get_buckets(counts, bkt, K, 0);
    for (i = 0; i < n; i++)
    {
        j = SA[i] - 1;
        if (j >= 0 && !TGET(j))
            SA[bkt[CHR(j)]++] = j;
    }

    // Induce S-type.
    // Find ends of buckets.
    get_buckets(counts, bkt, K, 1);
    for (i = n - 1; i >= 0; i--)
    {
        j = SA[i] - 1;
        if (j >= 0 && TGET(j))
            SA[--bkt[CHR(j)]] = j;
    }
}

int find_minima(int *lcp, int first, int last)
{
    int i = 0, min;

    while ((min = lcp[first + i]) < 0 && first + i < last)
        i++;
    for (i = first + i; i <= last; i++)
        if (lcp[i] < min && 0 <= lcp[i])
            min = lcp[i];

    return min;
}

void induce_sa_lcp(const unsigned char *t, int *SA, int *LCP, const void *s, const int *counts, int *bkt, const int *bs, const int *be, int n, int K, int cs)
{
    int i, j, k, m, *st, *bseam, previous, current, p;

    get_buckets(counts, bkt, K, 0);
    st = (int *)malloc(sizeof(int) * (K + 1));
    memset(st, -1, (K + 1) * sizeof(int));

    bseam = (int *)malloc(sizeof(int) * (K + 1));
    for (i = 0; i < K; i++)
        bseam[i] = bs[i] - 1;
    for (i = 0; i < n; i++)
        if (!TGET(i))
            bseam[CHR(i)]++;

    // Induce L-types
    for (i = 0; i < n; i++)
    {
        j = SA[i] - 1;

        if (j >= 0 && !TGET(j))
        {
            // It's the first element of bucket.
            if (st[CHR(j)] == -1)
            {
                LCP[bkt[CHR(j)]] = 0;
            }
            else
            {
                m = SA[bkt[CHR(j)] - 1] + 1;

                // Only first elements match.
                if (CHR(m) != CHR(j + 1))
                {
                    LCP[bkt[CHR(j)]] = 1;
                }
                else
                {
                    previous = st[CHR(j)];
                    LCP[bkt[CHR(j)]] = find_minima(LCP, previous + 1, i) + 1;
                }
            }

            st[CHR(j)] = i;
            SA[bkt[CHR(j)]++] = j;

            // L-S seam
            if (bkt[CHR(j)] - 1 == bseam[CHR(j)])
            {
                previous = SA[bkt[CHR(j)] - 1];
                current = -1;
                for (k = bkt[CHR(j)]; k < be[CHR(j)]; k++)
                {
                    if (LCP[k] == -2)
                    {
                        current = k;
                        break;
                    }
                }

                if (current == -1)
                    continue;
                p = 0;
                while (CHR(previous + p) == CHR(SA[current] + p) && SA[current] + p < n && previous + p < n)
                    p++;
                LCP[k] = p;
            }
        }
    }

    free(bseam);

    // Inducing S-types.
    get_buckets(counts, bkt, K, 1);
    memset(st, -1, (K + 1) * sizeof(int));

    for (i = n - 1; i >= 0; i--)
    {
        j = SA[i] - 1;

        if (j >= 0 && TGET(j))
        {
            SA[--bkt[CHR(j)]] = j;
            if (st[CHR(j)] != -1)
            {
                m = SA[bkt[CHR(j)] + 1] + 1;

                // Only first characters match.
                if (CHR(m) != CHR(j + 1))
                {
                    LCP[bkt[CHR(j)] + 1] = 1;
                }
                else
                {
                    previous = st[CHR(j)];
                    LCP[bkt[CHR(j)] + 1] = find_minima(LCP, i + 1, previous) + 1;
                }
            }

            // L-S seam.
            if (SA[bkt[CHR(j)] - 1] >= 0 && !TGET(SA[bkt[CHR(j)] - 1]) && bkt[CHR(j)] > bs[CHR(j)])
            {
                previous = SA[bkt[CHR(j)] - 1];
                current = SA[bkt[CHR(j)]];
                p = 0;
                while (CHR(previous + p) == CHR(current + p))
                    p++;
                LCP[bkt[CHR(j)]] = p;
            }
            else if (bkt[CHR(j)] == bs[CHR(j)])
            {
                // When S-type is at the start of the bucket.
                LCP[bkt[CHR(j)]] = 0;
            }

            st[CHR(j)] = i;
        }
    }

    free(st);
}

void sa_lcp_is(const void *s, int *SA, int *LCP, int n, int K, int cs, int level0)
{
    int i, j;
    unsigned char *t = (unsigned char *)malloc(n / 8 + 1);

    TSET(n - 2, 0);
    TSET(n - 1, 1);
    for (i = n - 3; i >= 0; i--)
        TSET(i, (CHR(i) < CHR(i + 1) || (CHR(i) == CHR(i + 1) && TGET(i + 1) == 1)) ? 1 : 0);

    // Sort all the S-substrings.
    int *counts = (int *)malloc(sizeof(int) * (K + 1));
    int *bkt = (int *)malloc(sizeof(int) * (K + 1));

    get_counts(s, counts, n, K, cs);
    get_buckets(counts, bkt, K, 1);
    for (i = 0; i < n; i++)
        SA[i] = -1;
    for (i = 1; i < n; i++)
        if (IS_LMS(i))
            SA[--bkt[CHR(i)]] = i;

    induce_sa(t, SA, s, counts, bkt, n, K, cs);

    free(bkt);
    free(counts);

    // Put all the sorted substrings into the first n1 items of SA.
    int n1 = 0;
    for (i = 0; i < n; i++)
        if (IS_LMS(SA[i]))
            SA[n1++] = SA[i];

    // Find the lexicographic names of all substrings.
    for (i = n1; i < n; i++)
        SA[i] = -1;
    int name = 0, prev = -1;

    for (i = 0; i < n1; i++)
    {
        int pos = SA[i];
        int diff = 0;
        for (int d = 0; d < n; d++)
        {
            if (prev == -1 || CHR(pos + d) != CHR(prev + d) || TGET(pos + d) != TGET(prev + d))
            {
                diff = 1;
                break;
            }
            else if (d > 0 && (IS_LMS(pos + d) || IS_LMS(prev + d)))
            {
                break;
            }
        }

        if (diff)
        {
            name++;
            prev = pos;
        }
        pos = (pos % 2 == 0) ? pos / 2 : (pos - 1) / 2;
        SA[n1 + pos] = name - 1;
    }

    for (i = n - 1, j = n - 1; i >= n1; i--)
        if (SA[i] >= 0)
            SA[j--] = SA[i];

    // Solve the reduced problem.
    int *SA1 = SA, *s1 = SA + n - n1;

    if (name < n1)
        sa_lcp_is((unsigned char *)s1, SA1, NULL, n1, name - 1, sizeof(int), 0);
    else
        for (i = 0; i < n1; i++)
            SA1[s1[i]] = i;

    // Induce the result for the original problem.
    counts = (int *)malloc(sizeof(int) * (K + 1));
    bkt = (int *)malloc(sizeof(int) * (K + 1));
    get_counts(s, counts, n, K, cs);
    get_buckets(counts, bkt, K, 1);
    for (i = 1, j = 0; i < n; i++)
        if (IS_LMS(i))
            s1[j++] = i;
    for (i = 0; i < n1; i++)
        SA1[i] = s1[SA1[i]];
    for (i = n1; i < n; i++)
        SA[i] = -1;

    // INDUCING THE LCP ARRAY: Put the sorted S*-suffixes into their corresponding S-buckets, without changing their order.
    if (level0)
    {
        int j, p, *bs, *be;

        memset(LCP, -1, sizeof(int) * n);
        bs = (int *)malloc(sizeof(int) * (K + 1));
        be = (int *)malloc(sizeof(int) * (K + 1));
        get_buckets(counts, bs, K, 0);
        get_buckets(counts, be, K, 1);

        LCP[0] = 0;
        j = SA[0];
        // Calculate LCP values for S*-suffixes.
        for (i = 1; i < n1; ++i)
        {
            p = 0;
            while (CHR(SA[i] + p) == CHR(j + p))
                p++;
            LCP[i] = p;
            j = SA[i];
        }

        for (i = n1 - 1; i >= 0; i--)
        {
            j = SA[i];
            SA[i] = -1;
            SA[--bkt[CHR(j)]] = j;

            p = LCP[i];
            LCP[i] = -1;
            LCP[bkt[CHR(j)]] = p;
        }

        // Mark L-S seam in LCP array.
        for (i = 0; i < K + 1; i++)
            if (bkt[i] != bs[i] && bkt[i] != be[i])
                LCP[bkt[i]] = -2;

        induce_sa_lcp(t, SA, LCP, s, counts, bkt, bs, be, n, K, cs);

        free(bs);
        free(be);
    }
    else
    {
        for (i = n1 - 1; i >= 0; i--)
        {
            j = SA[i];
            SA[i] = -1;
            SA[--bkt[CHR(j)]] = j;
        }
        induce_sa(t, SA, s, counts, bkt, n, K, cs);
    }

    free(counts);
    free(bkt);
    free(t);
}