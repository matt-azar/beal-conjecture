// Modular symbols for Gamma_0(N) over F_p (p = 31, or -DPMOD=p), dual ("flow") model.
// M^* = { phi : P^1(Z/N) -> F_p | phi(xS) = -phi(x), phi(x)+phi(xR)+phi(xR^2) = 0 }.
// Hecke: (T_l phi)(x) = sum over Heilbronn-Cremona matrices h of phi(x h).
// Requires N without elliptic points (S and R act freely on P^1(Z/N)).
// No dependencies beyond a C++17 compiler with OpenMP and AVX2. Usage and expected output: docs/modular-symbols-replay.md
#include <bits/stdc++.h>
#include <immintrin.h>
#include <omp.h>
using namespace std;
typedef long long ll; typedef unsigned char u8;
#ifndef PMOD
#define PMOD 31
#endif
static const int P = PMOD;
static int N, M, nV, nE, n;            // level, |P^1|, vertices, edges, dim M^*
static vector<int> pp, qq, radix; static vector<vector<int>> invt; static vector<ll> crt;
static vector<int> repc, repd, Smap, Rmap, vert, parentDart, bfs, coordDart;
static int inv31[P];

static int idx(ll c, ll d) {
  int res = 0;
  for (size_t i = 0; i < qq.size(); i++) {
    int q = qq[i], p = pp[i]; int cc = (int)(((c % q) + q) % q), dd = (int)(((d % q) + q) % q), li;
    if (cc % p) li = (int)((ll)dd * invt[i][cc] % q);
    else { if (dd % p == 0) return -1; li = q + (int)((ll)cc * invt[i][dd] % q) / p; }
    res = res * radix[i] + li;
  }
  return res;
}
static void setup() {
  int m = N;
  for (int p = 2; m > 1; p++) if (m % p == 0) { int q = 1; while (m % p == 0) { m /= p; q *= p; } pp.push_back(p); qq.push_back(q); }
  M = 1;
  for (size_t i = 0; i < qq.size(); i++) {
    int q = qq[i]; radix.push_back(q + q / pp[i]); M *= radix[i];
    vector<int> t(q, 0); for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if ((ll)a * b % q == 1) t[a] = b;
    if (q == 1) t[0] = 0; invt.push_back(t);
    ll other = N / q, e = 0; for (ll k = 0; k < q; k++) if (other * k % q == 1 % q) e = other * k; crt.push_back(e % N);
  }
  repc.resize(M); repd.resize(M);
  for (int i = 0; i < M; i++) {
    int r = i; ll c = 0, d = 0;
    for (int k = (int)qq.size() - 1; k >= 0; k--) {
      int li = r % radix[k]; r /= radix[k]; ll lc, ld;
      if (li < qq[k]) { lc = 1; ld = li; } else { lc = (ll)pp[k] * (li - qq[k]); ld = 1; }
      c = (c + lc * crt[k]) % N; d = (d + ld * crt[k]) % N;
    }
    repc[i] = (int)c; repd[i] = (int)d;
    if (idx(c, d) != i) { fprintf(stderr, "index mismatch\n"); exit(1); }
  }
  Smap.resize(M); Rmap.resize(M);
  for (int i = 0; i < M; i++) { Smap[i] = idx(repd[i], -repc[i]); Rmap[i] = idx(repd[i], -(ll)repc[i] - repd[i]); }
  for (int i = 0; i < M; i++) {
    if (Smap[i] == i || Smap[Smap[i]] != i) { fprintf(stderr, "S not a free involution\n"); exit(1); }
    if (Rmap[i] == i || Rmap[Rmap[Rmap[i]]] != i) { fprintf(stderr, "R not free of order 3\n"); exit(1); }
  }
  vert.assign(M, -1); nV = 0; vector<int> vdart;
  for (int i = 0; i < M; i++) if (vert[i] < 0) { vert[i] = vert[Rmap[i]] = vert[Rmap[Rmap[i]]] = nV++; vdart.push_back(i); }
  nE = M / 2;
  parentDart.assign(nV, -1); vector<char> seen(nV, 0), tree(M, 0);
  bfs.push_back(0); seen[0] = 1;
  for (size_t h = 0; h < bfs.size(); h++) {
    int v = bfs[h], x = vdart[v];
    for (int k = 0; k < 3; k++, x = Rmap[x]) {
      int y = Smap[x], w = vert[y];
      if (!seen[w]) { seen[w] = 1; parentDart[w] = y; tree[y] = tree[x] = 1; bfs.push_back(w); }
    }
  }
  if ((int)bfs.size() != nV) { fprintf(stderr, "graph not connected\n"); exit(1); }
  for (int i = 0; i < M; i++) if (!tree[i] && i < Smap[i]) coordDart.push_back(i);
  n = (int)coordDart.size();
  if (n != nE - nV + 1) { fprintf(stderr, "dimension mismatch\n"); exit(1); }
  for (int a = 1; a < P; a++) for (int b = 1; b < P; b++) if (a * b % P == 1) inv31[a] = b;
}
// coordinates on non-tree edges -> full flow
static void extend(const u8* co, u8* phi) {
  for (int k = 0; k < n; k++) { int x = coordDart[k]; phi[x] = co[k]; phi[Smap[x]] = (u8)((P - co[k]) % P); }
  for (int h = nV - 1; h >= 1; h--) {
    int p = parentDart[bfs[h]]; int s = phi[Rmap[p]] + phi[Rmap[Rmap[p]]];
    phi[p] = (u8)((2 * P - s) % P); phi[Smap[p]] = (u8)((P - phi[p]) % P);
  }
}
static bool isFlow(const u8* phi) {
  for (int i = 0; i < M; i++) {
    if ((phi[i] + phi[Smap[i]]) % P) return false;
    if ((phi[i] + phi[Rmap[i]] + phi[Rmap[Rmap[i]]]) % P) return false;
  }
  return true;
}
static vector<array<ll,4>> heilbronn(int p) {
  vector<array<ll,4>> L;
  if (p == 2) { L = {{1,0,0,2},{2,0,0,1},{2,1,0,1},{1,0,1,2}}; return L; }
  L.push_back({1, 0, 0, p});
  for (int r = -(p / 2); r <= p / 2; r++) {
    ll x1 = p, x2 = -r, y1 = 0, y2 = 1, a = -p, b = r, c, x3, y3, q;
    L.push_back({x1, x2, y1, y2});
    while (b) {
      q = (ll)llround((double)a / (double)b);
      c = a - b * q; a = -b; b = c;
      x3 = q * x2 - x1; x1 = x2; x2 = x3;
      y3 = q * y2 - y1; y1 = y2; y2 = y3;
      L.push_back({x1, x2, y1, y2});
    }
  }
  return L;
}
struct Hecke { int l; vector<vector<int>> tab; };
static Hecke makeHecke(int l) {
  Hecke H; H.l = l; auto L = heilbronn(l); H.tab.assign(L.size(), vector<int>(M));
  #pragma omp parallel for
  for (size_t k = 0; k < L.size(); k++)
    for (int i = 0; i < M; i++)
      H.tab[k][i] = idx(repc[i] * L[k][0] + repd[i] * L[k][2], repc[i] * L[k][1] + repd[i] * L[k][3]);
  return H;
}
static void applyT(const Hecke& H, const u8* in, u8* out) {
  vector<unsigned> acc(M, 0);
  for (auto& t : H.tab) { const int* tp = t.data(); if (N % H.l) for (int i = 0; i < M; i++) acc[i] += in[tp[i]]; else for (int i = 0; i < M; i++) if (tp[i] >= 0) acc[i] += in[tp[i]]; }
  for (int i = 0; i < M; i++) out[i] = (u8)(acc[i] % P);
}
// out = prod_{a in S} (T - a) in
static void applyFilter(const Hecke& H, const vector<int>& S, const u8* in, u8* out) {
  vector<u8> cur(in, in + M), tmp(M);
  for (int a : S) { applyT(H, cur.data(), tmp.data()); for (int i = 0; i < M; i++) cur[i] = (u8)((tmp[i] + (P - a) * cur[i]) % P); }
  memcpy(out, cur.data(), M);
}
// ---- small dense linear algebra over F_31 ----
typedef vector<vector<u8>> Mat;
// row-reduce rows in place; returns pivot columns; drops zero rows
static vector<int> rref(Mat& A, int cols) {
  vector<int> piv; size_t r = 0;
  for (int j = 0; j < cols && r < A.size(); j++) {
    size_t s = r; while (s < A.size() && !A[s][j]) s++;
    if (s == A.size()) continue;
    swap(A[s], A[r]); int iv = inv31[A[r][j]];
    for (int t = j; t < cols; t++) A[r][t] = (u8)(A[r][t] * iv % P);
    #pragma omp parallel for schedule(dynamic, 16)
    for (size_t i = 0; i < A.size(); i++) if (i != r && A[i][j]) {
      int c = P - A[i][j]; u8* a = A[i].data(); const u8* b = A[r].data();
      for (int t = j; t < cols; t++) a[t] = (u8)((a[t] + c * b[t]) % P);
    }
    piv.push_back(j); r++;
  }
  A.resize(r); return piv;
}
// kernel {v : A v = 0} of an m x m matrix, as rows
static Mat kernel(Mat A, int m) {
  vector<int> piv = rref(A, m); vector<char> isp(m, 0); for (int j : piv) isp[j] = 1;
  Mat K;
  for (int f = 0; f < m; f++) if (!isp[f]) {
    vector<u8> v(m, 0); v[f] = 1;
    for (size_t i = 0; i < piv.size(); i++) v[piv[i]] = (u8)((P - A[i][f]) % P);
    K.push_back(v);
  }
  return K;
}
static Mat matmul(const Mat& A, const Mat& B, int m) {
  Mat C(m, vector<u8>(m));
  #pragma omp parallel for
  for (int i = 0; i < m; i++) {
    vector<unsigned> acc(m, 0);
    for (int k = 0; k < m; k++) if (A[i][k]) { unsigned a = A[i][k]; const u8* b = B[k].data(); for (int j = 0; j < m; j++) acc[j] += a * b[j]; if ((k & 2047) == 2047) for (int j = 0; j < m; j++) acc[j] %= P; }
    for (int j = 0; j < m; j++) C[i][j] = (u8)(acc[j] % P);
  }
  return C;
}
// A space is a list of coordinate vectors (length n) in reduced echelon form with pivots piv.
struct Space { Mat W; vector<int> piv; };
// Matrix C of T on the space: T w_i = sum_j C[i][j] w_j. Verifies invariance exactly.
static Mat heckeOn(const Space& Sp, const Hecke& H) {
  int m = (int)Sp.W.size(); Mat C(m, vector<u8>(m)); bool ok = true;
  #pragma omp parallel for schedule(dynamic, 4)
  for (int i = 0; i < m; i++) {
    vector<u8> phi(M), psi(M); extend(Sp.W[i].data(), phi.data()); applyT(H, phi.data(), psi.data());
    if (i < 3 && !isFlow(psi.data())) { ok = false; }
    vector<unsigned> acc(n, 0);
    for (int j = 0; j < m; j++) { unsigned c = psi[coordDart[Sp.piv[j]]]; C[i][j] = (u8)c; if (c) { const u8* w = Sp.W[j].data(); for (int t = 0; t < n; t++) acc[t] += c * w[t]; } if ((j & 2047) == 2047) for (int t = 0; t < n; t++) acc[t] %= P; }
    for (int t = 0; t < n; t++) if (acc[t] % P != psi[coordDart[t]]) { ok = false; break; }
  }
  if (!ok) { fprintf(stderr, "FAILED: T_%d does not preserve the space (or image is not a flow)\n", H.l); exit(1); }
  return C;
}
static Space cut(const Space& Sp, const Mat& C, const vector<int>& S) {
  int m = (int)Sp.W.size(); Mat D(m, vector<u8>(m, 0)); for (int i = 0; i < m; i++) D[i][i] = 1;
  for (int a : S) { Mat F = C; for (int i = 0; i < m; i++) F[i][i] = (u8)((F[i][i] + P - a) % P); D = matmul(D, F, m); }
  // rows convention: w_i -> sum_j D[i][j] w_j ; kernel vectors k with sum_i k_i D[i][.] = 0  => transpose
  Mat Dt(m, vector<u8>(m)); for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) Dt[j][i] = D[i][j];
  Mat K = kernel(Dt, m); Space R;
  for (auto& k : K) { vector<unsigned> acc(n, 0); for (int i = 0; i < m; i++) if (k[i]) { unsigned c = k[i]; const u8* w = Sp.W[i].data(); for (int t = 0; t < n; t++) acc[t] += c * w[t]; if ((i & 2047) == 2047) for (int t = 0; t < n; t++) acc[t] %= P; } vector<u8> v(n); for (int t = 0; t < n; t++) v[t] = (u8)(acc[t] % P); R.W.push_back(v); }
  R.piv = rref(R.W, n); return R;
}
static vector<pair<int, vector<int>>> readFilters(const char* fn) {
  vector<pair<int, vector<int>>> F; ifstream in(fn); string line;
  while (getline(in, line)) { istringstream ss(line); int l, a; if (!(ss >> l)) continue; vector<int> S; while (ss >> a) S.push_back(((a % P) + P) % P); F.push_back({l, S}); }
  return F;
}
static void saveSpace(const Space& Sp, const char* fn) {
  FILE* f = fopen(fn, "wb"); int m = (int)Sp.W.size(); fwrite(&m, 4, 1, f); fwrite(&n, 4, 1, f); fwrite(Sp.piv.data(), 4, m, f);
  for (auto& w : Sp.W) fwrite(w.data(), 1, n, f); fclose(f);
}
static Space loadSpace(const char* fn) {
  FILE* f = fopen(fn, "rb"); int m, nn; if (!f || fread(&m, 4, 1, f) != 1 || fread(&nn, 4, 1, f) != 1 || nn != n) { fprintf(stderr, "bad space file\n"); exit(1); }
  Space Sp; Sp.piv.resize(m); if (fread(Sp.piv.data(), 4, m, f) != (size_t)m) exit(1); Sp.W.assign(m, vector<u8>(n));
  for (auto& w : Sp.W) if (fread(w.data(), 1, n, f) != (size_t)n) exit(1); fclose(f); return Sp;
}
// Kernel of prod_{a in S}(T_l - a) on all of M^*, by dense Gauss-Jordan with AVX2.
static Space bigKernel(const Hecke& H, const vector<int>& S) {
  size_t stride = ((size_t)n + 31) & ~(size_t)31;
  u8* buf = (u8*)aligned_alloc(32, stride * n); memset(buf, 0, stride * n);
  double t0 = omp_get_wtime(); bool ok = true;
  #pragma omp parallel for schedule(dynamic, 16)
  for (int j = 0; j < n; j++) {
    vector<u8> e(n, 0), phi(M), z(M); e[j] = 1; extend(e.data(), phi.data());
    if (j % 4099 == 0) { int x0 = 0; if ((phi[x0] + phi[Rmap[x0]] + phi[Rmap[Rmap[x0]]]) % P || !isFlow(phi.data())) ok = false; }
    applyFilter(H, S, phi.data(), z.data());
    if (j % 4099 == 0 && !isFlow(z.data())) ok = false;
    for (int i = 0; i < n; i++) buf[(size_t)i * stride + j] = z[coordDart[i]];
  }
  if (!ok) { fprintf(stderr, "FAILED flow check in matrix build\n"); exit(1); }
  fprintf(stderr, "matrix built in %.0fs\n", omp_get_wtime() - t0);
  vector<u8*> row(n); for (int i = 0; i < n; i++) row[i] = buf + (size_t)i * stride;
  u8* mult = (u8*)aligned_alloc(32, stride * P); vector<int> piv; int rank = 0; const __m256i v31 = _mm256_set1_epi8(P);
  for (int j = 0; j < n; j++) {
    int s = rank; while (s < n && !row[s][j]) s++;
    if (s == n) continue;
    swap(row[s], row[rank]); u8* pr = row[rank]; int iv = inv31[pr[j]]; size_t j0 = (size_t)j & ~(size_t)31;
    for (size_t t = j0; t < stride; t++) pr[t] = (u8)(pr[t] * iv % P);
    for (int c = 1; c < P; c++) { u8* mc = mult + (size_t)c * stride; for (size_t t = j0; t < stride; t++) mc[t] = (u8)(c * pr[t] % P); }
    #pragma omp parallel for schedule(static)
    for (int i = 0; i < n; i++) {
      if (i == rank) continue; int c = row[i][j]; if (!c) continue;
      const u8* mc = mult + (size_t)(P - c) * stride; u8* a = row[i];
      for (size_t t = j0; t < stride; t += 32) {
        __m256i x = _mm256_add_epi8(_mm256_load_si256((const __m256i*)(a + t)), _mm256_load_si256((const __m256i*)(mc + t)));
        _mm256_store_si256((__m256i*)(a + t), _mm256_min_epu8(x, _mm256_sub_epi8(x, v31)));
      }
    }
    piv.push_back(j); rank++;
    if (j % 2000 == 0) fprintf(stderr, "col %d rank %d  %.0fs\n", j, rank, omp_get_wtime() - t0);
  }
  fprintf(stderr, "rank %d of %d in %.0fs\n", rank, n, omp_get_wtime() - t0);
  vector<char> isp(n, 0); for (int j : piv) isp[j] = 1; Space Sp;
  for (int f = 0; f < n; f++) if (!isp[f]) {
    vector<u8> v(n, 0); v[f] = 1; for (int i = 0; i < rank; i++) v[piv[i]] = (u8)((P - row[i][f]) % P);
    Sp.W.push_back(v); Sp.piv.push_back(f);
  }
  free(buf); free(mult); return Sp;
}
int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: ms N eig l1 l2.. | ms N big FILTERS OUT | ms N run SPACE FILTERS [skip] | ms N dump SPACE OUTPREFIX l1 l2..\n"); return 1; }
  N = atoi(argv[1]); setup(); string mode = argv[2];
  printf("N=%d |P1|=%d V=%d E=%d dim=%d\n", N, M, nV, nE, n); fflush(stdout);
  if (mode == "eig") {           // validation at small level: eigenvalue multiplicities in F_31
    Space Sp; Sp.W.assign(n, vector<u8>(n, 0)); for (int i = 0; i < n; i++) { Sp.W[i][i] = 1; Sp.piv.push_back(i); }
    vector<Mat> Cs;
    for (int k = 3; k < argc; k++) {
      Hecke H = makeHecke(atoi(argv[k])); Mat C = heckeOn(Sp, H); Cs.push_back(C);
      printf("T_%d (%zu matrices): ", H.l, H.tab.size());
      for (int a = 0; a < P; a++) { Mat F(n, vector<u8>(n)); for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) F[j][i] = (u8)((C[i][j] + (i == j ? P - a : 0)) % P); int d = (int)kernel(F, n).size(); if (d) printf(" %d^%d", a > 15 ? a - P : a, d); }
      printf("\n");
    }
    for (size_t a = 0; a < Cs.size(); a++) for (size_t b = a + 1; b < Cs.size(); b++) if (matmul(Cs[a], Cs[b], n) != matmul(Cs[b], Cs[a], n)) printf("NOT COMMUTING %zu %zu\n", a, b);
    return 0;
  }
  if (mode == "big") {
    auto F = readFilters(argv[3]); Hecke H = makeHecke(F[0].first);
    Space Sp = bigKernel(H, F[0].second); printf("kernel of filter at %d: dim %zu\n", F[0].first, Sp.W.size()); saveSpace(Sp, argv[4]); return 0;
  }
  if (mode == "run") {
    Space Sp = loadSpace(argv[3]); auto F = readFilters(argv[4]); printf("start dim %zu\n", Sp.W.size());
    for (auto& f : F) {
      if (Sp.W.empty()) break; Hecke H = makeHecke(f.first); Mat C = heckeOn(Sp, H); Sp = cut(Sp, C, f.second);
      printf("after l=%d (%zu allowed residues, %zu Heilbronn matrices): dim %zu\n", f.first, f.second.size(), H.tab.size(), Sp.W.size()); fflush(stdout);
    }
    printf("FINAL dim %zu\n", Sp.W.size());
    if (getenv("MS_SAVE")) saveSpace(Sp, getenv("MS_SAVE"));
    int m = (int)Sp.W.size();
    for (int k = 5; k < argc && m; k++) {
      Hecke H = makeHecke(atoi(argv[k])); Mat C = heckeOn(Sp, H); printf("T_%d on survivors:", H.l); int tot = 0;
      for (int a = 0; a < P; a++) { Mat F(m, vector<u8>(m)); for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) F[j][i] = (u8)((C[i][j] + (i == j ? P - a : 0)) % P); int d = (int)kernel(F, m).size(); tot += d; if (d) printf(" %d^%d", a > 15 ? a - P : a, d); }
      printf("   (eigenvectors over F_p: %d of %d)\n", tot, m); fflush(stdout);
    }
    return 0;
  }
  if (mode == "dump") {         // ms N dump SPACE OUTPREFIX l1 l2 ... : matrices of T_l on a saved Hecke-stable space
    Space Sp = loadSpace(argv[3]); int m = (int)Sp.W.size(); printf("space dim %d\n", m);
    vector<vector<u8>> Phi(m, vector<u8>(M));
    #pragma omp parallel for
    for (int i = 0; i < m; i++) extend(Sp.W[i].data(), Phi[i].data());
    for (int a = 5; a < argc; a++) {
      int l = atoi(argv[a]); if (N % l == 0) { fprintf(stderr, "l divides N\n"); return 1; }
      auto L = heilbronn(l); double t0 = omp_get_wtime();
      vector<vector<unsigned>> acc(m, vector<unsigned>(n, 0));
      #pragma omp parallel
      {
        vector<int> tp(n); vector<vector<unsigned>> loc(m, vector<unsigned>(n, 0));
        #pragma omp for schedule(dynamic, 8) nowait
        for (size_t k = 0; k < L.size(); k++) {
          for (int t = 0; t < n; t++) { int x = coordDart[t]; tp[t] = idx((ll)repc[x] * L[k][0] + (ll)repd[x] * L[k][2], (ll)repc[x] * L[k][1] + (ll)repd[x] * L[k][3]); }
          for (int i = 0; i < m; i++) { const u8* ph = Phi[i].data(); unsigned* ac = loc[i].data(); for (int t = 0; t < n; t++) ac[t] += ph[tp[t]]; }
        }
        #pragma omp critical
        for (int i = 0; i < m; i++) for (int t = 0; t < n; t++) acc[i][t] += loc[i][t];
      }
      // full image of the first basis vector, to check that it is a flow
      bool ok = true;
      if (m) {
        vector<u8> psi0(M);
        #pragma omp parallel for schedule(dynamic, 256)
        for (int x = 0; x < M; x++) { unsigned s = 0; const u8* ph = Phi[0].data(); for (size_t k = 0; k < L.size(); k++) s += ph[idx((ll)repc[x] * L[k][0] + (ll)repd[x] * L[k][2], (ll)repc[x] * L[k][1] + (ll)repd[x] * L[k][3])]; psi0[x] = (u8)(s % P); }
        if (!isFlow(psi0.data())) ok = false;
        for (int t = 0; t < n; t++) if (psi0[coordDart[t]] != acc[0][t] % P) ok = false;
      }
      Mat C(m, vector<u8>(m));
      #pragma omp parallel for
      for (int i = 0; i < m; i++) {
        vector<unsigned> chk(n, 0);
        for (int j = 0; j < m; j++) { unsigned c = acc[i][Sp.piv[j]] % P; C[i][j] = (u8)c; if (c) { const u8* w = Sp.W[j].data(); for (int t = 0; t < n; t++) chk[t] += c * w[t]; } if ((j & 2047) == 2047) for (int t = 0; t < n; t++) chk[t] %= P; }
        for (int t = 0; t < n; t++) if (chk[t] % P != acc[i][t] % P) { ok = false; break; }
      }
      if (!ok) { fprintf(stderr, "FAILED: T_%d does not preserve the space (or image is not a flow)\n", l); return 1; }
      string fn = string(argv[4]) + "_" + to_string(l) + ".txt"; FILE* f = fopen(fn.c_str(), "w"); fprintf(f, "%d\n", m);
      for (int i = 0; i < m; i++) { for (int j = 0; j < m; j++) fprintf(f, "%d ", C[i][j]); fprintf(f, "\n"); } fclose(f);
      printf("T_%d: %zu Heilbronn matrices, invariance and flow checks passed, %.0fs -> %s\n", l, L.size(), omp_get_wtime() - t0, fn.c_str()); fflush(stdout);
    }
    return 0;
  }
  return 1;
}
