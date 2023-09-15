#include <bits/stdc++.h>
using namespace std;

#define MAXN 500005
#define ll long long
#define pi pair<ll*, ll*>

template<int MOD> struct Fp
{
    long long val;
    constexpr Fp(long long v = 0) noexcept : val(v% MOD)
    {
        if (val < 0) val += MOD;
    }
    constexpr int getmod() const { return MOD; }
    constexpr Fp operator - () const noexcept
    {
        return val ? MOD - val : 0;
    }
    constexpr Fp operator + (const Fp& r) const noexcept { return Fp(*this) += r; }
    constexpr Fp operator - (const Fp& r) const noexcept { return Fp(*this) -= r; }
    constexpr Fp operator * (const Fp& r) const noexcept { return Fp(*this) *= r; }
    constexpr Fp operator / (const Fp& r) const noexcept { return Fp(*this) /= r; }
    constexpr Fp& operator += (const Fp& r) noexcept
    {
        val += r.val;
        if (val >= MOD) val -= MOD;
        return *this;
    }
    constexpr Fp& operator -= (const Fp& r) noexcept
    {
        val -= r.val;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr Fp& operator *= (const Fp& r) noexcept
    {
        val = val * r.val % MOD;
        return *this;
    }
    constexpr Fp& operator /= (const Fp& r) noexcept
    {
        long long a = r.val, b = MOD, u = 1, v = 0;
        while (b)
        {
            long long t = a / b;
            a -= t * b, swap(a, b);
            u -= t * v, swap(u, v);
        }
        val = val * u % MOD;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr bool operator == (const Fp& r) const noexcept
    {
        return this->val == r.val;
    }
    constexpr bool operator != (const Fp& r) const noexcept
    {
        return this->val != r.val;
    }
    friend constexpr istream& operator >> (istream& is, Fp<MOD>& x) noexcept
    {
        is >> x.val;
        x.val %= MOD;
        if (x.val < 0) x.val += MOD;
        return is;
    }
    friend constexpr ostream& operator << (ostream& os, const Fp<MOD>& x) noexcept
    {
        return os << x.val;
    }
    friend constexpr Fp<MOD> modpow(const Fp<MOD>& r, long long n) noexcept
    {
        if (n == 0) return 1;
        if (n < 0) return modpow(modinv(r), -n);
        auto t = modpow(r, n / 2);
        t = t * t;
        if (n & 1) t = t * r;
        return t;
    }
    friend constexpr Fp<MOD> modinv(const Fp<MOD>& r) noexcept
    {
        long long a = r.val, b = MOD, u = 1, v = 0;
        while (b)
        {
            long long t = a / b;
            a -= t * b, swap(a, b);
            u -= t * v, swap(u, v);
        }
        return Fp<MOD>(u);
    }
};

#define MOD 998244353
using Spmod = Fp<MOD>;

struct s
{
    s* fa;
    s* so[2];
    Spmod v, sum;
    Spmod lzAdd, lzMul;
    ll lzRev, sz;

    void init()
    {
        fa = so[0] = so[1] = nullptr;
        lzMul = 1;
        v = lzAdd = sum = 0;
        lzRev = sz = 0;
    }
};

#define pss pair<s*, s*>

s* rt = nullptr;

bool get(s* x)
{
    return (x == (x->fa)->so[1]);
}

bool chk(s* p)
{
    return (p != nullptr);
}

void pushDownAdd(s* p)
{
    if (p->lzMul != 1 || p->lzAdd != 0)
    {
        if (chk(p->so[0]))
        {
            p->so[0]->v = ((p->so[0]->v * p->lzMul) + p->lzAdd);
            p->so[0]->sum = ((p->so[0]->sum * p->lzMul) + (Spmod)p->so[0]->sz * p->lzAdd);
            p->so[0]->lzMul *= p->lzMul;
            p->so[0]->lzAdd = (p->so[0]->lzAdd * p->lzMul) + p->lzAdd;
        }
        if (chk(p->so[1]))
        {
            p->so[1]->v = ((p->so[1]->v * p->lzMul) + p->lzAdd);
            p->so[1]->sum = ((p->so[1]->sum * p->lzMul) + (Spmod)p->so[1]->sz * p->lzAdd);
            p->so[1]->lzMul *= p->lzMul;
            p->so[1]->lzAdd = (p->so[1]->lzAdd * p->lzMul) + p->lzAdd;
        }
        p->lzMul = 1, p->lzAdd = 0;
    }
}

void pushDownRev(s* p)
{
    if (p->lzRev)
    {
        swap(p->so[0], p->so[1]);
        if (chk(p->so[0])) p->so[0]->lzRev ^= 1;
        if (chk(p->so[1])) p->so[1]->lzRev ^= 1;
        p->lzRev = 0;
    }
}

void pushDown(s* p)
{
    pushDownAdd(p);
    pushDownRev(p);
}

void pullUp(s* p)
{
    p->sz = 1;
    p->sum = p->v;
    if (chk(p->so[0]))
    {
        p->sz += p->so[0]->sz;
        p->sum += p->so[0]->sum;
    }

    if (chk(p->so[1]))
    {
        p->sz += p->so[1]->sz;
        p->sum += p->so[1]->sum;
    }
}

void rotate(s* p) // automatic check between left rotate and right rotate
{
    pushDown(p->fa);
    pushDown(p);
    if (!get(p)) // left
    {
        int x;
        bool y = chk(p->fa->fa);
        if (y) x = get(p->fa);
        p->fa->so[0] = p->so[1]; p->so[1] = p->fa;
        p->fa = p->so[1]->fa; p->so[1]->fa = p;
        if (y) p->fa->so[x] = p;
        if (chk(p->so[1]->so[0]))
            p->so[1]->so[0]->fa = p->so[1];
        pullUp(p->so[1]);
        pullUp(p);
    }
    else // right
    {
        int x;
        bool y = chk(p->fa->fa);
        if (y) x = get(p->fa);
        p->fa->so[1] = p->so[0]; p->so[0] = p->fa;
        p->fa = p->so[0]->fa; p->so[0]->fa = p;
        if (y) p->fa->so[x] = p;
        if (chk(p->so[0]->so[1]))
            p->so[0]->so[1]->fa = p->so[0];
        pullUp(p->so[0]);
        pullUp(p);
    }
}

s* splay(s* n)
{
    while (n != nullptr && n->fa != nullptr)
    {
        if (n->fa->fa == nullptr)
        {
            rotate(n);
            break;
        }
        else if (get(n) == get(n->fa))
        {
            rotate(n->fa);
            rotate(n);
        }
        else
        {
            rotate(n);
            rotate(n);
        }
    }

    return rt = n;
}

s* find(s* cur, int ind)
{
    if (!chk(cur))
        return cur;
    if (ind > cur->sz && ind < 1)
        return nullptr;
    pushDown(cur);

    int lsz = 0;
    if (chk(cur->so[0]))
        lsz = cur->so[0]->sz;
    if (lsz > (ind - 1))
        return find(cur->so[0], ind);
    else if (lsz < (ind - 1))
        return find(cur->so[1], ind - lsz - 1);
    else
    {
        splay(cur);
        return cur;
    }
}

s* merge(s* lt, s* rt)
{
    if (!chk(lt))
        return rt;
    else if (!chk(rt))
        return lt;

    s* ml = find(lt, lt->sz);
    splay(ml);

    ml->so[1] = rt;
    rt->fa = ml;

    if (chk(rt)) pullUp(rt);
    if (chk(ml)) pullUp(ml);

    return ml;
}

pss split(s* t, int ind)
{
    if (ind > t->sz) return make_pair(t, nullptr);
    if (ind < 1) return make_pair(nullptr, t);

    s* p = find(t, ind);
    splay(p);

    s* other = nullptr;
    if (p->so[1] != nullptr)
    {
        other = p->so[1];
        other->fa = nullptr;
    }

    p->so[1] = nullptr;
    if (chk(p)) pullUp(p);
    if (chk(other)) pullUp(other);

    return make_pair(p, other);
}

s* ins(s* p, int va, int ind)
{
    s* np = new s;
    np->init();
    np->lzMul = 1, np->v = np->sum = va, np->sz = 1;

    if (!chk(p) || ind > p->sz) // empty tree or at the end of the tree
    {
        merge(p, np);
        return splay(np);
    }

    pss n = split(p, ind - 1);
    merge(merge(n.first, np), n.second);
    return splay(np);
}

s* del(s* p, int ind)
{
    if (ind > p->sz || ind < 1) return nullptr;
    pss p1 = split(p, ind - 1);
    pss p2 = split(p1.second, 1); // the middle point (basically p2.first) is out of the tree.
    return splay(merge(p1.first, p2.second));
}

void rangeAdd(s* p, int l, int r, int a, int b)
{
    pss p1 = split(p, l - 1);
    pss p2 = split(p1.second, r - l + 1);

    p2.first->v = p2.first->v * a + b;
    p2.first->sum = p2.first->sum * a + p2.first->sz * b;
    p2.first->lzMul = a, p2.first->lzAdd = b;
    merge(p1.first, merge(p2.first, p2.second));
}

void rangeRev(s* p, int l, int r)
{
    pss p1 = split(p, l - 1);
    pss p2 = split(p1.second, r - l + 1);

    p2.first->lzRev ^= 1;
    merge(p1.first, merge(p2.first, p2.second));
}

Spmod getSum(s* p, int l, int r)
{
    pss p1 = split(p, l - 1);
    pss p2 = split(p1.second, r - l + 1);

    pullUp(p2.first);
    Spmod ans = p2.first->sum;

    merge(p1.first, merge(p2.first, p2.second));

    return ans;
}

ll n, q;

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr), cout.tie(nullptr);

    cin >> n >> q;

    for (int i = 1, q; i <= n; i++)
    {
        cin >> q;
        ins(rt, q, i);
    }

    for (int i = 1, c, l, r, a, b; i <= q; i++)
    {
        cin >> c;
        if (c == 0)
        {
            cin >> l >> a;
            ins(rt, a, l + 1);
        }
        else if (c == 1)
        {
            cin >> l;
            del(rt, l + 1);
        }
        else if (c == 2)
        {
            cin >> l >> r;
            rangeRev(rt, l + 1, r);
        }
        else if (c == 3)
        {
            cin >> l >> r >> a >> b;
            rangeAdd(rt, l + 1, r, a, b);
        }
        else
        {
            cin >> l >> r;
            cout << getSum(rt, l + 1, r) << "\n";
        }
    }

    return 0;
}

// https://judge.yosupo.jp/problem/dynamic_sequence_range_affine_range_sum