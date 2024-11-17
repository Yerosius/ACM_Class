// Created by Nikolay Budin

#ifdef DEBUG
#  define _GLIBCXX_DEBUG
#endif
#include <bits/stdc++.h>
#define ff first
#define ss second
#define szof(x) ((int)x.size())
#ifndef LOCAL
#  define cerr __get_ce
#endif

using namespace std;
typedef long long ll;
typedef long double ld;
typedef pair<int, int> pii;
typedef unsigned long long ull;
int const INF = (int)1e9 + 1e3;
ll const INFL = (ll)1e18 + 1e6;
#ifdef LOCAL
	mt19937 tw(9450189);
#else
	mt19937 tw(chrono::high_resolution_clock::now().time_since_epoch().count());
#endif
uniform_int_distribution<ll> ll_distr;
ll rnd(ll a, ll b) { return ll_distr(tw) % (b - a + 1) + a; }

typedef tuple<vector<int>, vector<int>, vector<int>, vector<int>, int> value;

const int MOD = 998'244'353;

void add(int& a, int b) {
	a += b;
	if (a >= MOD) {
		a -= MOD;
	}
}

int sum(int a, int b) {
	add(a, b);
	return a;
}

int mult(int a, int b) {
	return (ll) a * b % MOD;
}

int mpow(int a, int b) {
	int ret = 1;
	while (b) {
		if (b & 1) {
			ret = mult(ret, a);
		}
		a = mult(a, a);
		b >>= 1;
	}
	return ret;
}

int inv(int num) {
	return mpow(num, MOD - 2);
}

const int bp = 20, sz = 1 << bp;
int roots[sz];
int perm[sz];
int arra[sz], arrb[sz];

void fft(int arr[], int cbp) {
	int csz = 1 << cbp;
	for (int i = 0; i < csz; ++i) {
		if (perm[i] >> (bp - cbp) > i) {
			swap(arr[i], arr[perm[i] >> (bp - cbp)]);
		}
	}

	for (int i = 1, root_shift = sz / 2; i < csz; i *= 2, root_shift /= 2) {
		for (int j = 0; j < csz; j += i * 2) {
			for (int k = 0, root_pos = 0; k < i; ++k, root_pos += root_shift) {
				int tmp = mult(arr[j + i + k], roots[root_pos]);
				arr[j + i + k] = sum(arr[j + k], MOD - tmp);
				add(arr[j + k], tmp);
			}
		}
	}
}

vector<int> mult(vector<int> const& a, vector<int> const& b) {
	if (!szof(a) || !szof(b)) {
		return {};
	}
	int cbp = 0;
	while (1 << cbp < szof(a) + szof(b) - 1) {
		++cbp;
	}
	for (int i = 0; i < szof(a); ++i) {
		arra[i] = a[i];
	}
	fill(arra + szof(a), arra + (1 << cbp), 0);
	for (int i = 0; i < szof(b); ++i) {
		arrb[i] = b[i];
	}
	fill(arrb + szof(b), arrb + (1 << cbp), 0);
	fft(arra, cbp);
	fft(arrb, cbp);
	for (int i = 0; i < 1 << cbp; ++i) {
		arra[i] = mult(arra[i], arrb[i]);
	}
	fft(arra, cbp);
	reverse(arra + 1, arra + (1 << cbp));
	vector<int> ret;
	int coef = inv(1 << cbp);
	for (int i = 0; i < 1 << cbp; ++i) {
		ret.push_back(mult(arra[i], coef));
	}
	while (szof(ret) && ret.back() == 0) {
		ret.pop_back();
	}

	return ret;
}

void add(vector<int>& a, vector<int> const& b) {
	a.resize(max(szof(a), szof(b)));
	for (int i = 0; i < szof(b); ++i) {
		add(a[i], b[i]);
	}
}

vector<int> sum(vector<int> a, vector<int> const& b) {
	add(a, b);
	return a;
}

vector<int> add_pos(vector<int> a, int pos, int val) {
	if (pos == -1) {
		return a;
	}
	if (szof(a) <= pos) {
		a.resize(pos + 1);
	}
	add(a[pos], val);
	return a;
}

vector<int> shift(vector<int> a, int n) {
	if (n == -1) {
		return {};
	}
	a.resize(szof(a) + n);
	rotate(a.begin(), a.end() - n, a.end());
	return a;
}

void solve() {
	int n;
	cin >> n;
	string border, center;
	cin >> border >> center;
	function<value(int, int)> rec = [&](int l, int r) {
		if (l + 1 == r) {
			if (center[l] == '-') {
				return value({}, {}, {}, {}, 0);
			}
			if (center[l] == 'B') {
				return value({}, {}, {}, {1}, 0);
			}
			return value({}, {}, {}, {0, 1}, 0);
		}
		int m = (l + r) / 2;
		auto [l00, l01, l10, l11, lw] = rec(l, m);
		auto [r00, r01, r10, r11, rw] = rec(m, r);
		vector<int> t00 = mult(add_pos(l01, lw, 1), add_pos(r10, rw, 1));
		vector<int> t01 = mult(add_pos(l01, lw, 1), r11);
		vector<int> t10 = mult(l11, add_pos(r10, rw, 1));
		vector<int> t11 = mult(l11, r11);
		if (border[m - 1] != '-') {
			vector<int> tmp00 = sum(mult(add_pos(l01, lw, 1), r00), mult(l00, add_pos(r10, rw, 1)));
			vector<int> tmp01 = sum(mult(add_pos(l01, lw, 1), r01), sum(mult(l00, r11), shift(l01, rw)));
			vector<int> tmp10 = sum(mult(l10, add_pos(r10, rw, 1)), sum(mult(l11, r00), shift(r10, lw)));
			vector<int> tmp11 = sum(mult(l11, add_pos(r01, rw, 1)), mult(add_pos(l10, lw, 1), r11));
			if (border[m - 1] == 'W') {
				tmp00.insert(tmp00.begin(), 0);
				tmp01.insert(tmp01.begin(), 0);
				tmp10.insert(tmp10.begin(), 0);
				tmp11.insert(tmp11.begin(), 0);
			}
			add(t00, tmp00);
			add(t01, tmp01);
			add(t10, tmp10);
			add(t11, tmp11);
		}
		// cerr << "seg " << l << " " << r << " " << (lw + rw + (border[m - 1] == 'W')) << endl;
		// for (auto const& q : {t00, t01, t10, t11}) {
		// 	for (int num : q) {
		// 		cerr << num << " ";
		// 	}
		// 	cerr << endl;
		// }
		return value(t00, t01, t10, t11, (lw == -1 || rw == -1 || border[m - 1] == '-') ? -1 : (lw + rw + (border[m - 1] == 'W')));
	};

	auto [t00, t01, t10, t11, totw] = rec(0, n);
	vector<int> ans = t11;
	if (border.back() != '-') {
		vector<int> tmp = sum(t01, t10);
		if (border.back() == 'W') {
			tmp.insert(tmp.begin(), 0);
		}
		add(ans, tmp);
	}
	ans.resize(n + 1);
	for (int num : ans) {
		cout << num << " ";
	}
	cout << "\n";
}


int main() {
#ifdef LOCAL
	auto start_time = clock();
	cerr << setprecision(3) << fixed;
#endif
	cout << setprecision(15) << fixed;
	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	int root = 2;
	for (; ; ++root) {
		if (mpow(root, sz / 2) == MOD - 1) {
			break;
		}
	}

	roots[0] = 1;
	for (int i = 1; i < sz; ++i) {
		perm[i] = (perm[i >> 1] >> 1) | ((i & 1) << (bp - 1));
		roots[i] = mult(roots[i - 1], root);
	}

	int test_count = 1;
	// cin >> test_count;
	for (int test = 1; test <= test_count; ++test) {
		solve();
	}
	
#ifdef LOCAL
	auto end_time = clock();
	cerr << "Execution time: " << (end_time - start_time) * (int)1e3 / CLOCKS_PER_SEC << " ms\n";
#endif
}
