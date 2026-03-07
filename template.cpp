// ----------------------- CPP LIBRARIES --------------------
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#ifdef CPH
#include "debugtemplate.cpp"
#else
#define debug(...)
#endif
// ----------------------- MACROS --------------------
#define ll long long
#define nl "\n" 
#define sp " "
#define iloop(i, k, n) for (ll i = k; i < n; i++)
#define dloop(i, n, k) for (ll i = n; i >= k; i--)
#define rall(v) v.rbegin(), v.rend()
#define all(v) v.begin(), v.end()
#define pb push_back
template<typename T> using pq = priority_queue<T>;
template<typename T> using minpq = priority_queue<T, vector<T>, greater<T>>;
#define ff first
#define ss second
#define vi vector<ll>
#define pii pair<ll, ll>
#define mii map<ll, ll>
#define si set<ll>
#define msi multiset<ll>
#define vii vector<pii>
#define vvi vector<vi>
//------------------------ CONSTANT --------------------
const ll mod = 1e9 + 7;
const ll inf = 1e18;
const ll ninf = -1e18;
const ll N = 1e5 + 5;
//------------------------ ORDERED SET --------------------
template <typename T>
using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
template <typename T>
using ordered_pset = tree<pair<T,T>, null_type, less<pair<T,T>>, rb_tree_tag, tree_order_statistics_node_update>;
template <typename T>
using ordered_mset = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update>;
// order_of_key(x) -> returns the number of elements strictly smaller than x
// find_by_order(x) -> returns an iterator to the element at the xth index (0-indexed)
//-------------------------- MODINT -------------------------
template <int MOD>
struct ModInt {
    int val;
    
    // Constructors
    ModInt(long long v = 0) {
        if (v < 0) v = v % MOD + MOD;
        if (v >= MOD) v %= MOD;
        val = v;
    }

    // Arithmetic Assignments
    ModInt& operator+=(const ModInt& other) { val += other.val; if (val >= MOD) val -= MOD; return *this; }
    ModInt& operator-=(const ModInt& other) { val -= other.val; if (val < 0) val += MOD; return *this; }
    ModInt& operator*=(const ModInt& other) { val = (long long)val * other.val % MOD; return *this; }
    ModInt& operator/=(const ModInt& other) { return *this *= other.inv(); }

    // Arithmetic Operators
    friend ModInt operator+(ModInt a, const ModInt& b) { return a += b; }
    friend ModInt operator-(ModInt a, const ModInt& b) { return a -= b; }
    friend ModInt operator*(ModInt a, const ModInt& b) { return a *= b; }
    friend ModInt operator/(ModInt a, const ModInt& b) { return a /= b; }

    // Unary Negation & Increment/Decrement
    ModInt operator-() const { return ModInt(val ? MOD - val : 0); }
    ModInt& operator++() { val = val == MOD - 1 ? 0 : val + 1; return *this; }
    ModInt operator++(int) { ModInt before = *this; ++*this; return before; }
    ModInt& operator--() { val = val == 0 ? MOD - 1 : val - 1; return *this; }
    ModInt operator--(int) { ModInt before = *this; --*this; return before; }

    // Equality
    bool operator==(const ModInt& other) const { return val == other.val; }
    bool operator!=(const ModInt& other) const { return val != other.val; }

    // Exponentiation
    ModInt pow(long long p) const {
        if (p < 0) return inv().pow(-p);
        ModInt a = *this, res = 1;
        while (p > 0) {
            if (p & 1) res *= a;
            a *= a;
            p >>= 1;
        }
        return res;
    }
    
    // Modular Inverse (Using Fermat's Little Theorem - assumes MOD is prime)
    ModInt inv() const { return pow(MOD - 2); }

    // Fast I/O
    friend ostream& operator<<(ostream& stream, const ModInt& m) { return stream << m.val; }
    friend istream& operator>>(istream& stream, ModInt& m) {
        long long v; stream >> v;
        m = ModInt(v);
        return stream;
    }
};
//-------------------------- BIGINT -------------------------
struct BigInt { 
    static const int BASE = 1e9;
    vector<int> a;
    int sign;

    BigInt() : sign(1) {}
    BigInt(long long v) { *this = v; }
    BigInt(const string& s) { read(s); }

    void operator=(const BigInt& v) { sign = v.sign; a = v.a; }
    void operator=(long long v) {
        sign = 1;
        a.clear();
        if (v < 0) { sign = -1; v = -v; }
        for (; v > 0; v = v / BASE) a.push_back(v % BASE);
    }

    bool isZero() const { return a.empty(); }
    BigInt abs() const { BigInt res = *this; res.sign = 1; return res; }

    void trim() {
        while (!a.empty() && !a.back()) a.pop_back();
        if (a.empty()) sign = 1;
    }

    BigInt operator+(const BigInt& v) const {
        if (isZero()) return v;
        if (v.isZero()) return *this;
        if (sign == v.sign) {
            BigInt res = v;
            for (int i = 0, carry = 0; i < max(a.size(), v.a.size()) || carry; ++i) {
                if (i == res.a.size()) res.a.push_back(0);
                res.a[i] += carry + (i < a.size() ? a[i] : 0);
                carry = res.a[i] >= BASE;
                if (carry) res.a[i] -= BASE;
            }
            return res;
        }
        return sign == 1 ? *this - (-v) : v - (-*this);
    }

    BigInt operator-(const BigInt& v) const {
        if (v.isZero()) return *this;
        if (isZero()) return -v;
        if (sign == v.sign) {
            if (abs() >= v.abs()) {
                BigInt res = *this;
                for (int i = 0, carry = 0; i < v.a.size() || carry; ++i) {
                    res.a[i] -= carry + (i < v.a.size() ? v.a[i] : 0);
                    carry = res.a[i] < 0;
                    if (carry) res.a[i] += BASE;
                }
                res.trim();
                return res;
            }
            return -(v - *this);
        }
        return sign == 1 ? *this + (-v) : -(-*this + v);
    }

    static vector<int> karatsuba(const vector<int>& a, const vector<int>& b) {
        int n = a.size(), m = b.size();
        if (n == 0 || m == 0) return {};
        
        // Use simple multiplication for small sizes
        if (n < 32 || m < 32) {
            vector<int> res(n + m);
            for (int i = 0; i < n; ++i) {
                if (!a[i]) continue;
                long long carry = 0;
                for (int j = 0; j < m || carry; ++j) {
                    long long cur = res[i + j] + a[i] * 1ll * (j < m ? b[j] : 0) + carry;
                    res[i + j] = int(cur % BASE);
                    carry = int(cur / BASE);
                }
            }
            while (res.size() > 1 && res.back() == 0) res.pop_back();
            return res;
        }

        int k = max(n, m) / 2;
        vector<int> a1(a.begin(), a.begin() + min(n, k));
        vector<int> a2(a.begin() + min(n, k), a.end());
        vector<int> b1(b.begin(), b.begin() + min(m, k));
        vector<int> b2(b.begin() + min(m, k), b.end());

        vector<int> z0 = karatsuba(a1, b1);
        vector<int> z2 = karatsuba(a2, b2);

        // (a1 + a2)
        vector<int> a1a2 = a1;
        for (int i = 0, carry = 0; i < a2.size() || carry; ++i) {
            if (i == a1a2.size()) a1a2.push_back(0);
            a1a2[i] += carry + (i < a2.size() ? a2[i] : 0);
            carry = a1a2[i] >= BASE;
            if (carry) a1a2[i] -= BASE;
        }

        // (b1 + b2)
        vector<int> b1b2 = b1;
        for (int i = 0, carry = 0; i < b2.size() || carry; ++i) {
            if (i == b1b2.size()) b1b2.push_back(0);
            b1b2[i] += carry + (i < b2.size() ? b2[i] : 0);
            carry = b1b2[i] >= BASE;
            if (carry) b1b2[i] -= BASE;
        }

        vector<int> z1 = karatsuba(a1a2, b1b2);

        // z1 = z1 - z0 - z2
        auto sub = [](vector<int>& x, const vector<int>& y) {
            for (int i = 0, carry = 0; i < y.size() || carry; ++i) {
                if (i == x.size()) x.push_back(0);
                x[i] -= carry + (i < y.size() ? y[i] : 0);
                carry = x[i] < 0;
                if (carry) x[i] += BASE;
            }
            while (x.size() > 1 && x.back() == 0) x.pop_back();
        };
        sub(z1, z0);
        sub(z1, z2);

        // Combine: z0 + z1 * BASE^k + z2 * BASE^(2k)
        int maxSize = max({z0.size(), z1.size() + k, z2.size() + 2 * k});
        vector<int> res(maxSize);
        
        for (int i = 0; i < z0.size(); ++i) res[i] = z0[i];
        for (int i = 0, carry = 0; i < z1.size() || carry; ++i) {
            if (i + k >= res.size()) res.push_back(0);
            long long cur = res[i + k] + (i < z1.size() ? z1[i] : 0) + carry;
            res[i + k] = int(cur % BASE);
            carry = int(cur / BASE);
        }
        for (int i = 0, carry = 0; i < z2.size() || carry; ++i) {
            if (i + 2 * k >= res.size()) res.push_back(0);
            long long cur = res[i + 2 * k] + (i < z2.size() ? z2[i] : 0) + carry;
            res[i + 2 * k] = int(cur % BASE);
            carry = int(cur / BASE);
        }
        
        while (res.size() > 1 && res.back() == 0) res.pop_back();
        return res;
    }

    BigInt operator*(const BigInt& v) const {
        if (isZero() || v.isZero()) return BigInt();
        BigInt res;
        res.sign = sign * v.sign;
        res.a = karatsuba(a, v.a);
        res.trim();
        return res;
    }

    void operator*=(int v) {
        if (v == 0) { sign = 1; a.clear(); return; }
        if (v < 0) { sign = -sign; v = -v; }
        for (int i = 0, carry = 0; i < a.size() || carry; ++i) {
            if (i == a.size()) a.push_back(0);
            long long cur = a[i] * 1ll * v + carry;
            carry = (int)(cur / BASE);
            a[i] = (int)(cur % BASE);
        }
        trim();
    }
    BigInt operator*(int v) const { BigInt res = *this; res *= v; return res; }

    friend pair<BigInt, BigInt> divmod(const BigInt& a1, const BigInt& b1) {
        if (b1.isZero()) throw invalid_argument("BigInt: Division by zero");
        
        int norm = BASE / (b1.a.back() + 1);
        BigInt a = a1.abs() * norm;
        BigInt b = b1.abs() * norm;
        BigInt q, r;
        q.a.resize(a.a.size());

        for (int i = a.a.size() - 1; i >= 0; i--) {
            r *= BASE;
            r += a.a[i];
            int s1 = r.a.size() <= b.a.size() ? 0 : r.a[b.a.size()];
            int s2 = r.a.size() <= b.a.size() - 1 ? 0 : r.a[b.a.size() - 1];
            int d = ((long long) BASE * s1 + s2) / b.a.back();
            r -= b * d;
            while (r < 0) {
                r += b, --d;
            }
            q.a[i] = d;
        }

        q.sign = a1.sign * b1.sign;
        r.sign = a1.sign;
        q.trim();
        r.trim();
        return {q, r / norm};
    }

    BigInt operator/(const BigInt& v) const { return divmod(*this, v).first; }
    BigInt operator%(const BigInt& v) const { return divmod(*this, v).second; }

    void operator/=(int v) {
        if (v == 0) throw invalid_argument("BigInt: Division by zero");
        if (v < 0) { sign = -sign; v = -v; }
        for (int i = (int)a.size() - 1, rem = 0; i >= 0; --i) {
            long long cur = a[i] + rem * 1ll * BASE;
            a[i] = (int)(cur / v);
            rem = (int)(cur % v);
        }
        trim();
    }
    BigInt operator/(int v) const { BigInt res = *this; res /= v; return res; }

    long long operator%(long long v) const {
        if (v == 0) throw invalid_argument("BigInt: Modulo by zero");
        long long absV = v < 0 ? -v : v;
        long long m = 0;
        for (int i = (int)a.size() - 1; i >= 0; --i) {
            m = (a[i] + m * (BASE % absV)) % absV;
        }
        return sign == 1 ? m : -m;
    }

    BigInt operator-() const {
        BigInt res = *this;
        if (!isZero()) res.sign = -sign;
        return res;
    }

    void operator+=(const BigInt& v) { *this = *this + v; }
    void operator-=(const BigInt& v) { *this = *this - v; }
    void operator*=(const BigInt& v) { *this = *this * v; }
    void operator/=(const BigInt& v) { *this = *this / v; }

    bool operator<(const BigInt& v) const {
        if (isZero() && v.isZero()) return false;
        if (sign != v.sign) return sign < v.sign;
        if (a.size() != v.a.size()) return a.size() * sign < v.a.size() * v.sign;
        for (int i = a.size() - 1; i >= 0; i--)
            if (a[i] != v.a[i]) return a[i] * sign < v.a[i] * sign;
        return false;
    }

    bool operator>(const BigInt& v) const { return v < *this; }
    bool operator<=(const BigInt& v) const { return !(v < *this); }
    bool operator>=(const BigInt& v) const { return !(*this < v); }
    bool operator==(const BigInt& v) const { return !(*this < v) && !(v < *this); }
    bool operator!=(const BigInt& v) const { return *this < v || v < *this; }

    void read(const string& s) {
        sign = 1;
        a.clear();
        int pos = 0;
        while (pos < s.size() && (s[pos] == '-' || s[pos] == '+')) {
            if (s[pos] == '-') sign = -sign;
            ++pos;
        }
        for (int i = s.size() - 1; i >= pos; i -= 9) {
            int x = 0;
            for (int j = max(pos, i - 8); j <= i; j++) x = x * 10 + s[j] - '0';
            a.push_back(x);
        }
        trim();
    }

    friend istream& operator>>(istream& stream, BigInt& v) {
        string s; stream >> s;
        v.read(s);
        return stream;
    }

    friend ostream& operator<<(ostream& stream, const BigInt& v) {
        if (v.isZero()) return stream << 0;
        if (v.sign == -1) stream << '-';
        stream << v.a.back();
        for (int i = (int)v.a.size() - 2; i >= 0; --i)
            stream << setw(9) << setfill('0') << v.a[i];
        return stream;
    }
};
//------------------------ HASHING --------------------------
struct Hash {
    int n;
    const long long m1 = 1e9 + 7, m2 = 1e9 + 9;
    const long long p1 = 313, p2 = 317;
    vector<long long> h1, h2, pw1, pw2;

    Hash(const string& s) {
        n = s.size();
        h1.assign(n + 1, 0); h2.assign(n + 1, 0);
        pw1.assign(n + 1, 1); pw2.assign(n + 1, 1);
        
        for (int i = 0; i < n; i++) {
            h1[i + 1] = (h1[i] * p1 + s[i]) % m1;
            h2[i + 1] = (h2[i] * p2 + s[i]) % m2;
            pw1[i + 1] = (pw1[i] * p1) % m1;
            pw2[i + 1] = (pw2[i] * p2) % m2;
        }
    }
    // Queries the hash of substring s[l...r] (0-indexed, inclusive)
    pair<long long, long long> get(long long l, long long r) {
        long long res1 = (h1[r + 1] - h1[l] * pw1[r - l + 1]) % m1;
        if (res1 < 0) res1 += m1;
        
        long long res2 = (h2[r + 1] - h2[l] * pw2[r - l + 1]) % m2;
        if (res2 < 0) res2 += m2;
        
        return {res1, res2};
    }
};
// ----------------------- UTILITIES --------------------
inline ll add(ll a, ll b, ll m = mod) {a = (a + b) % m;return (a < 0) ? a + m : a;}
inline ll sub(ll a, ll b, ll m = mod) {a = (a - b) % m;return (a < 0) ? a + m : a;}
inline ll mul(ll a, ll b, ll m = mod) {return (a * b) % m;}
ll binpow(ll a, ll b, ll m = mod) {a %= m;ll res = 1; 
    while (b > 0) {if (b & 1) res = (1LL * res * a) % m; a = (1LL * a * a) % m;b >>= 1;}return res; }
ll modinverse(ll n, ll m = mod) {return binpow(n, m - 2, m);}
inline ll moddiv(ll a, ll b, ll m = mod) {return mul(a, modinverse(b, m), m);}
namespace io {
    template <typename T, typename F>
    istream &operator>>(istream &cin, pair<T, F> &pr) {cin >> pr.first >> pr.second;return cin;}
    template <typename T, typename F>
    ostream &operator<<(ostream &cout, const pair<T, F> &pr) {cout << pr.first << " " << pr.second;return cout;}
    template <typename T>
    istream &operator>>(istream &cin, vector<T> &vec) { for (T &i : vec) cin >> i; return cin;}
    template <typename T> 
    ostream &operator<<(ostream &cout, const vector<T> &vec) { for (const T &i : vec) cout << i << " "; return cout;}
}
using namespace io;
using mint = ModInt<mod>;
// ----------------------- SOLUTION --------------------
void solve()
{
    
}
int main()
{
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);
    ll test = 1;
    cin >> test;
    while (test--)
    {
        solve();
    }
    return 0;
}
