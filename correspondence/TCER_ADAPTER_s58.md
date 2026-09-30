# TCER_ADAPTER_s58 — Kane–Kim の帰結から TCER へ（通常数学の adapter）

作成 2026-09-26 (s58, agora)。GATE28 A1 の成果物。論文 Appendix A の Lemma A.8（本稿の番号、Lean root なし）とその証明の詳細版。
**s60 注（GATE30）:** r49 から論文の正規形と分類は §10 に移り、番号は A.k → 10.k（Lemma A.8 → Lemma 10.8）。本文書の本文は r48 時点の番号のまま残す。
状態語: 通常数学の証明（Lean では TCER は明示仮定のまま。公理ではない）。原論文にない定理番号は使わない。

## 1. Lean の型（`ResearchUpgrade/TCERBridge.lean` l.52, l.61、変更なし）

```lean
def LocalPrimRep (S : Matrix (Fin 3) (Fin 3) ℤ) (d : ℕ) (ρ : Fin 3 → ℤ) (N : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, ∃ x : Fin 3 → ℤ,
    ((p : ℤ) ^ e ∣ QS S (ρ + (d : ℤ) • x) - N) ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + (d : ℤ) • x) i

def TernaryCosetEventualRepresentation : Prop :=
  ∀ (S : Matrix (Fin 3) (Fin 3) ℤ) (d : ℕ) (ρ : Fin 3 → ℤ),
    S.IsSymm → (∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) → 0 < d →
    ∃ (bad : Finset ℕ) (E : Finset ℕ), (∀ p ∈ bad, p.Prime) ∧ (∀ e ∈ E, 0 < e) ∧
      ∀ b : ℕ → ℕ, ∃ N₀ : ℤ, ∀ N : ℤ, N₀ ≤ N → LocalPrimRep S d ρ N →
        (∀ p ∈ bad, ¬ (p : ℤ) ^ (b p + 1) ∣ N) →
        (∀ e ∈ E, ¬ ∃ q : ℚ, (N : ℚ) = (e : ℚ) * q ^ 2) →
        ∃ x : Fin 3 → ℤ, QS S (ρ + (d : ℤ) • x) = N
```

## 2. 出典（刊行版で逐語確認、s58 `s58_evidence/literature/kk_full.txt` md5 e71848bf）

Kane–Kim, *Theta series of ternary quadratic lattice cosets*, Selecta Math. **32** (2026), art. 5, DOI 10.1007/s00029-025-01110-0。

- p.4–5（導入部）: E の係数は Shimura の coset 版 Siegel–Weil 公式により局所表現密度の積（"kind of explicit ... in the sense that one may
  write it as a product of local representation densities"）。bad 素数で付値有界かつ局所表現されるとき "it grows at least like n^{1/2−ε}"。
  U の係数は有限個の平方類に台（Thm 5.6）。f の係数は Duke により ≪ n^{3/7+ε}。
  帰結: "every sufficiently-large positive integer n which has bounded divisibility at the "bad" primes, is locally represented by
  L + ν, and does not belong to any of the finitely many exceptional square classes is represented by L + ν."
- p.5–6（§2）: coset = aL + ν、ν ∈ L、導手（shifted lattice L + ν/a について a·v₀ ∈ L となる最小の a）がちょうど a。L は整（B(L,L) ⊆ ℤ）。
- 下界を述べた番号付き命題は KK にない（全文検索）。本稿は p.5 の帰結として引用し、自稿の番号付き補題として特殊化する。

## 3. 補題（論文 Lemma A.8 の和訳。s59 で原始性を本文にそろえた — E-29-1, E-29-2）

S を正定値の整対称 3×3 行列、d ≥ 1、ρ ∈ ℤ³ とする。有限個の素数と有限個の正整数 e があって、それらの素数での付値の任意の上界 b に対し
N₀ ≥ 1 が存在し、次が成り立つ: N ≥ N₀ が、ρ + dℤ³ により各素数冪を法として原始的に表現され、それらの素数で v_p(N) ≤ b(p) を満たし、
どの e についても e·(有理数の平方) でないならば、ある x ∈ ℤ³ で N = Q_S(ρ + dx)。特に TCER が成り立つ。

ここで「N が ρ + dℤ³ により p^e を法として原始的に表現される」とは、ある x ∈ ℤ³ で Q_S(ρ + dx) − N が p^e で割り切れ、かつ ρ + dx の座標のうち
p で割れないものがあることをいう（ベクトルは p と e に依存してよい）。これは TCER の局所仮定 `LocalPrimRep` そのもので、原始性は x ではなく
表現ベクトル ρ + dx にかかる。証明の第一段 (a) はこの仮定を使う: S = I₃、d = 2、ρ = 0 では 4 = Q_S(2, 0, 0) は各素数冪を法として表現されるが、
2 を法として原始的には表現されない。通常の局所表現を仮定する版は述べず、使わない。

（s58 版の §3 見出しは「論文 Lemma A.8 と同文」だったが、§3 には「（原始的に）」があり本文にはなかった。GATE29 #125/#126 で訂正。）

## 4. 証明（adapter の各段）

**(a) coset の正規化。** ある素数 p が d と ρ の全座標を割るなら、ρ + dℤ³ のすべての点は全座標が p で割れるので、`LocalPrimRep` の
原始性条件が p で満たされない。仮定を満たす N は存在せず、TCER はこの coset について空に成り立つ（bad = E = ∅、N₀ 任意）。
そうでなければ gcd(d, ρ₁, ρ₂, ρ₃) = 1 であり、ρ/d を ℤ³ に入れる最小の正整数は d。よって ρ + dℤ³ は KK の意味で導手 d の coset
dL + ρ（L = ℤ³、B(x, y) = xᵀSy、Q(x) = B(x, x)）。L は整。

**(b) 原始性を忘れる → compactness。** 素数 p を固定し、X_e = {x ∈ ℤ_p³ : Q(ρ + dx) ≡ N (mod pᵉ)} と置く。`LocalPrimRep` から各 X_e は
整数点を含み非空。X_e は閉集合、X_{e+1} ⊆ X_e、ℤ_p³ はコンパクトなので ∩_e X_e ≠ ∅。その点 x で Q(ρ + dx) = N（ℤ_p 上の表現）。
実素点では N > 0 と S の正定値性で表現される（(e) の N₀ ≥ 1 がここで効く）。よって N は KK の意味で coset に局所表現される。
原始性は捨てるだけで、KK 側に原始版の主張を要求しない。

**(c) 付値上界。** N ≠ 0 のとき、¬ p^{b(p)+1} | N ⟺ v_p(N) ≤ b(p)。KK の "bounded divisibility at the bad primes" は、bad 素数での
付値に固定上界 b を置くこと。bad 素数の集合は coset だけで決まり、b より先に選ばれる。

**(d) 有限個の例外平方類。** U の台は有限個の平方類 tℤ²（t > 0、Thm 5.6）。E をそれらの t の集合とする。仮定
「どの e ∈ E についても N ≠ e·q²（q ∈ ℚ）」は N ∉ tℤ² より強く、安全側。

**(e) 閾値。** KK の「十分大」の閾値を N_src として N₀ = max(1, N_src)。N₀ ≥ 1 により N > 0。

**(f) 指数の比較（ε = 1/56）。** 上の条件の下で r(N) = a_E(N) + a_U(N) + a_f(N)。例外平方類の外では a_U(N) = 0。
a_E(N) ≥ c·N^{1/2−ε}、|a_f(N)| ≤ C·N^{3/7+ε}。1/2 − 1/56 = 27/56、3/7 + 1/56 = 25/56 なので
r(N) ≥ cN^{27/56} − CN^{25/56} = N^{25/56}(cN^{1/28} − C) > 0（N > (2C/c)^{28} のとき）。
c > 0 は coset と付値上界 b に、C は coset にのみ依存する。有効な値は主張しない。

**(g) 量化の順序。** coset（S, d, ρ）→ bad 素数と例外類 E → 付値上界 b → 閾値 N₀ → N。KK の順序と同じで、TCER の型の順序とも一致する。□

## 5. 仮定の対照表

| TCER の要素 | KK 側 | 本 adapter の段 |
|---|---|---|
| S 整対称・正定値 | 正定値三元整格子 L、B(x,y) = xᵀSy | (a) |
| coset ρ + dℤ³、d > 0 | 導手 d の coset dL + ρ | (a)（非原始なら空） |
| `LocalPrimRep S d ρ N` | 局所表現（原始性なし） | (b) |
| ∀ p ∈ bad, ¬ p^{b p+1} ∣ N | bad 素数で付値有界 | (c) |
| ∀ e ∈ E, N ≠ e·q² | 有限個の例外平方類を避ける | (d) |
| ∃ N₀, N₀ ≤ N | 十分大（非有効） | (e) |
| ∃ x, QS S (ρ + d•x) = N | 個別 coset による表現（genus ではない） | (f) |

## 6. 形式化の境界

Lean は TCER を明示的な仮定として受け取る（`hT : TernaryCosetEventualRepresentation`）。`#print axioms` が標準 3 公理だけであっても、
TCER が証明されたことにはならない。通常数学: 本 adapter と KK p.5 により TCER が成り立ち、一般 full NF と（m ≥ 2 で）共通傾き特徴付けが従う。
Lean: TCER の型から元の定義への含意を検証済み。残る課題は、TCER そのものの形式化、またはこの応用で解析理論を使わない別証明。
新しい算術予想（原始版など）は加えていない。
