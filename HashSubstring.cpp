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
    pair<long long, long long> get(int l, int r) {
        long long res1 = (h1[r + 1] - h1[l] * pw1[r - l + 1]) % m1;
        if (res1 < 0) res1 += m1;
        
        long long res2 = (h2[r + 1] - h2[l] * pw2[r - l + 1]) % m2;
        if (res2 < 0) res2 += m2;
        
        return {res1, res2};
    }
};
