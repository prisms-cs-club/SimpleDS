#include <bits/stdc++.h>
using namespace std;

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

/************************************/

#define ll long long
#define pll pair<ll, ll>
#define pii pair<int, int>
#define ff first
#define ss second
#define MAXN ((ll) 1e5)
#define INF 1e18
#define MOD 998244353
using mint = Fp<MOD>;

/************************************/

struct sgt
{
    ll n;
    ll cnt = 0;
    ll rt = 0;
    ll sgl, sgr;
    vector<mint> v, lzt;
    vector<ll> ls, rs;
    sgt(int _n) : n(_n), v(n << 2), lzt(n << 2), ls(n << 2), rs(n << 2)
    {
        sgl = 0, sgr = n - 1;
    }

    void init(ll p) { v[p] = 0, lzt[p] = 1, ls[p] = 0, rs[p] = 0; }
    
    void pushDown(ll p)
    {
        if (!ls[p]) ls[p] = ++cnt, init(cnt);
        if (!rs[p]) rs[p] = ++cnt, init(cnt);

        if (lzt[p] != 1)
        {
            v[ls[p]] *= lzt[p]; lzt[ls[p]] = lzt[p];
            v[rs[p]] *= lzt[p]; lzt[rs[p]] = lzt[p];
            lzt[p] = 1;
        }
    }

    void pullUp(ll p)
    {
        v[p] = v[ls[p]] + v[rs[p]];
    }

    mint query(ll p, ll ql, ll qr, ll cl, ll cr)
    {
        pushDown(p);

        if (ql <= cl && cr <= qr)
            return v[p];
        if (cl > qr || cr < ql)
            return 0;

        ll mid = (cl + cr) >> 1;
        return query(ls[p], ql, qr, cl, mid) + query(rs[p], ql, qr, mid + 1, cr);

        pullUp(p);
    }
    mint query(ll ql, ll qr) { return query(rt, ql, qr, sgl, sgr); }

    void update(ll p, ll ql, ll qr, ll cl, ll cr, mint value)
    {
        pushDown(p);

        if (ql <= cl && cr <= qr)
        {
            v[p] = value;
            return;
        }
        if (cl > qr || cr < ql)
            return;

        ll mid = (cl + cr) >> 1;
        update(ls[p], ql, qr, cl, mid, value);
        update(rs[p], ql, qr, mid + 1, cr, value);

        pullUp(p);
    }
    void update(ll ql, ll qr, mint value) { update(rt, ql, qr, sgl, sgr, value); }

    void multi(ll p, ll ql, ll qr, ll cl, ll cr, mint value)
    {
        pushDown(p);

        if (ql <= cl && cr <= qr)
        {
            lzt[p] *= value;
            v[p] *= value;
            return;
        }
        if (cl > qr || cr < ql)
            return;

        ll mid = (cl + cr) >> 1;
        multi(ls[p], ql, qr, cl, mid, value);
        multi(rs[p], ql, qr, mid + 1, cr, value);

        pullUp(p);
    }
    void multi(ll ql, ll qr, mint value) { multi(rt, ql, qr, sgl, sgr, value); }
};

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr), cout.tie(nullptr);

    sgt x(11);
    x.update(0, 0, 10);
    x.update(1, 1, 2);
    cout << x.query(0, 1) << endl;
    x.multi(0, 1, 2);
    cout << x.query(0, 1) << endl;

    return 0;
}
