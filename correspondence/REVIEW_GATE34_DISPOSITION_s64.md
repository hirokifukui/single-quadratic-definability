# REVIEW_GATE34_DISPOSITION_s64 — GPT の r52 レビュー（GPT 呼称 R52）の処理

作成 2026-09-30 (s64, agora)。対象 = `GPT_REVIEW_GATE34_20260930_{A,B,D,E}` と `_delivery/`。
**封緘済 r52（`~/Downloads/mpup_gpt_r52_20260928.zip` sha256 `9e0a0f9b…bc9d`）とその展開ツリー（r53 の BASE）は編集しない。訂正はすべて次の生成（r53）に束ねる。**

四分（我々の誤り／解釈違い・保留／向こうの誤り／事実確認）。GPT の数値・行番号・主張は、再導出または現物照合を経たものだけを受け入れた。
**GPT 同梱スクリプト（`evidence/run_checks.py`）は走らせていない**（読んで対象を確認しただけ）。GPT が再実行したのは我々の検査器 9 本で、下の §0.2 で同じ 9 本を我々も再実行した。
GPT が審査したのは core 分割 `APAL_PUBLIC_CORE_mpup_gpt_r52_20260928.zip`（sha256 `bec83196…6a5b` = split 記録・~/Downloads の実物・GPT 記載の三者一致）。history ZIP は GPT 未受領・未検査。
GPT 自身が「Lean/lake の独立 build、Sage、GitHub CI 実走、PDF 再組版、実 locator での final build、history ZIP、外部調査は未実施」と限界を明記している。

**台帳番号**: GATE33 の台帳は #206–#223（#224 の既出は SESSION_CLOSE_s63 と起動文の指示のみ、grep で確認）。本台帳は **#224 から**。正誤は **E-34-x**。

---

## 0. 受領と逐語保存（完了）

- 現物: チャット添付と `~/Downloads/APAL_R52_review_and_Claude_tasks.zip`（09-30 14:04 着）。両者 sha256 `2db1be4a…5b77`（一致）、md5 `6c0728f8…`、56 934 B、
  24 エントリ、ディレクトリ項目 0、**接頭ディレクトリあり**（`apal_r52_review_delivery/`）。R51 と違い **`DELIVERY_SHA256SUMS` と `README.md` は同梱されていない**。中継物 `~/lean/s64_evidence/intake/`。
- `intake/intake_gate34.py` `8971d931`（s63 `intake_gate33.py` `338ca91a` の複製。ZIP・期待 sha256・TAG・接頭辞・対応表を変更し、GPT 和の段を ABSENT 表示に置換。元ファイル md5 不変）→ ログ `1e1b03b8`:
  CRC 検査 None（全エントリ正常）、byte 比較 **25/25**（md 4・delivery 20・原 zip 1）、`unzip -p` 経由 **24/24**、仕込み対照（1 バイト反転）**捕捉**。`REVIEW_SHA256SUMS` `89e7e256` 25 行。
  - `GPT_REVIEW_GATE34_20260930_A_r52_review.md` `93cbc2f7`、105 行（原名 `APAL_R52_REVIEW.md`）
  - `…_B_closeout_tasks_for_claude.md` `acf68b33`、33 行（`CLAUDE_R52_CLOSEOUT_TASKS.md`、2 課題）
  - `…_D_execution_receipt.md` `9a5e1caa`、24 行（`EXECUTION_RECEIPT_R52.md`）
  - `…_E_source_evidence.md` `bdf13ab5`、485 行（`SOURCE_EVIDENCE_R52.md`。我々のファイルの逐語抜粋 → r53 で配布するなら parallel_prose_control で宣言が要る、s61 罠 4）
  - `GPT_REVIEW_GATE34_20260930_delivery/`: 原 zip、`REPORT_SCOPE_R52.patch`（`15cf7f9f`、38 行）、`evidence/` 19 点、`REVIEW_SHA256SUMS`。

## 0.1 起動プロトコル（s64 冒頭、実施）

| 項目 | 期待（SESSION_CLOSE_s63 §2） | 実測 |
|---|---|---|
| hostname | agora | agora（ssh なし。execute_command は agora 上） |
| HANDOFF / SESSION_CLOSE_s63 | 先頭 "s63 CLOSED … r52 sealed … POSTED to GPT" 02e18e2c / 1fb37cde | 同 / 同（CLOSE は全文、HANDOFF は先頭を読了） |
| static（`static_s64.sh` 18559abb、`s64_evidence/startup/` の写しで実行） | close 時ログ 61f7296f | `startup/static_s64_at_s64_start.log` **61f7296f**（diff 0 = 全行一致） |
| pin | d46bd453…、v4.31.0-rc1 | 同（static log 内） |
| counters（detach） | 1577/1542/0/0/0 | RU_AXIOMS_EXIT=0、**1577/1542/0/0/0**、FREE 35、CAPS_MISSING 0、EXIT=0（`startup/counters_s64.log` b199169c = s63 close と同一バイト、2 分未満） |
| statement_diff | 1092/1092・298/298・FAIL 0 | 同（static log 内） |
| parity | 127/0 | PARITY_FILES=127 DIFF=0（static log 内） |

**食い違いなし。**

## 0.2 照合の道具（s64_evidence）

| 道具 | md5 | 結果 |
|---|---|---|
| `cas/leg1_sympy_s64.py`（s63 `36723727` の複製、無改変） | 36723727 | **17/17**、仕込み **6/6** 捕捉、sympy 1.14.0。ログ `8442526d`（s63 ログと同一バイト） |
| `cas/leg2_sage_s64.sage`（s63 `24f11364` の複製、無改変、detach） | 24f11364 | **12/12**、仕込み **5/5** 捕捉、Sage 10.8。ログ `97d52ffc`（s63 と同一バイト） |
| GPT の `evidence/sympy_rerun.log` と我々の leg1 ログ | — | GPT 1621 B = 我々の 1605 B ＋ 末尾 16 B（`\n--- STDERR ---\n`）。**先頭 1605 B は byte 同一**。仕込み（1 バイト反転）は捕捉 |
| `probe/probe_gate34.lean`（s63 `probe_gate33.lean` 42525819 の複製 ＋ GPT が挙げた 22 名の `#check`） | c7e59c23 | 22 名すべて解決。エラーは仕込み 2 件のみ = **捕捉**。出力 `fce61929` |
| `facts/facts_gate34.py`（新規。core・r51 core とも ~/Downloads の split zip を新規展開） | 1f6f188f | **12/12 一致、不一致 0**。ログ `140052b3` |
| `facts/coverage_gate34.py`（新規。登録行 ↔ 二つの報告、仕込み付き） | 689c3f17 | 下の #232。ログ `f40e61a6` |
| `facts/excerpts_gate34.py`（s63 `excerpts_gate33.py` 78a80130 の複製。R52 の見出し・行書式に合わせて正規表現のみ変更） | 7eb3bf87 | **15 ブロック・354 行・不一致 0・所在不明 0**。パスのない 4 ブロック（JSON 1、PaperClaimTypeReport 3 行）は別に照合し、3 行とも実ログの行と逐語一致。仕込み（1 文字改変）は不一致 1 として**捕捉**。ログ `3e529a06` |
| 我々の検査器 9 本の再実行（`facts/rerun_gate34.sh` d9185ed9、core 新規展開の写し、`PYTHONDONTWRITEBYTECODE=1`、detach） | — | core verify EXIT 0（CLEANROOM_REFERENCE=ok、CORE_SHIPPING_EXIT=0）、`--cleanroom` 3/3、checksum 8/8、paper claims 47/0、controls 16/16、statement_diff 1092/1092・298/298、SymPy 17/17、signoff 6/6。**8 本のログが GPT の同名ログと、GPT 側末尾 `--- STDERR ---` を除いて byte 同一**。写しと core の差 0（`__pycache__` なし） |
| Blueprint 再生成（配布 `tools/gen_blueprint.py` と、パッチ後の写し `12f26bd8`、core の写しに対して別出力へ） | — | 元の生成器: 3 ファイルとも配布物と byte 同一。パッチ後: `blueprint_nodes.tsv`・`dep_graph.dot` は byte 同一、`BLUEPRINT.md` は案内 2 行 → 3 行の差のみ |
| パッチ試走（`tools/patchtrial/`、pkg の 3 ソースの写し） | — | pkg の 3 ソースは core と byte 同一（f872af4f / 33086118 / 12c533ee）。`patch --dry-run` 成功、実適用後 12f26bd8 / 1b4ac0b2 / 7632ef8d。試走前後で pkg 実物の md5 不変 |
| 開発全体の Lean ソース走査（注釈・文字列を除去し、`axiom` 宣言・`sorry`・`sorryAx`・`native_decide`・`ofReduceBool`・`trustCompiler`） | — | 該当ファイル 0（#233 の根拠の一つ） |

---

## 1. 台帳（#224 から）

| # | GPT の記述 | 分類 | 現物・再導出 | 処理 |
|---|---|---|---|---|
| 224 | 書簡 GATE33 の問いへの答え: 前回 3 課題 **3/3 合格**、数学的 P0 なし、ビルド失敗・証拠欠落に当たる P1 なし。「数学の凍結を維持し、技術的な投稿候補として受け入れる」。通常の重大修正レビューとしては終了。数学・登録声明の再審査を次の必須工程にしない | 事実確認 | A §結論・§6、B §判定 | **受領。** 候補を公開・投稿用に固定してよいという判定と読む。ただし条件が一つ付く: 新規 P2（#232）の案内文訂正を最終生成に入れ、「現在の正しい検査を一度実行」してから、著者が判断する候補として返すこと。独立した全面再レビューは終了条件にしない（B-1 成果物欄）|
| 225 | E-33-1（README 手動ブロックの三つの `lake build`）合格。template・描画後 README・lakefile・fresh_build.sh・原ログと対応。今回の環境での実ビルドとは数えない | 事実確認 | 描画後 README l.52–54（`lake build` / `DiophCompression` / `ResearchUpgrade`）、抜粋 39 行一致 | 受領。**受け入れ** |
| 226 | E-33-2（CI）: 三ライブラリを build、DC・RU の audit を別 step、`working-directory: lean`、`shell: bash`・pipefail。ソースの静的確認で GitHub 実行成功の認定ではない | 事実確認 | ci.yml l.12–15・29–31・33–36・42–44 と一致（ほかに l.32 で `QuadraticWitnessInertiaCore` も build） | 受領。**受け入れ（静的）**。GitHub で走らせるまで CI 成功と書かない（B-2 Step 4 と同旨、既に我々の表記もそうなっている）|
| 227 | GATE33 課題 2 合格。チェックリストの PARTIAL は封緘前の記録で、最終 ZIP の検査成功により合格へ更新 | 事実確認 | GPT の根拠は GPT 自身の core 再検査（verify EXIT 0、cleanroom 3/3）で、**`core_gate.txt` は送っていない**。我々の同じ再実行もログ一致（§0.2）。封緘時の実 core ゲート（CLEANROOM_REFERENCE=ok、3/3、CORE_SHIPPING_EXIT 0）とも整合 | 受領。r53 の checklist では GATE33 課題 2 を「封緘時の実 core ゲートと GPT R52 の再検査で合格」と書く |
| 228 | s63 の追加変更（表紙の所属・email、Funding・利益相反、AI 宣言の参考文献直前への移動、abstract と序論の古典入力の明示）は著者の別途決定として扱い、前回課題の違反としない。所属・Funding・利益相反の事実は外部照会で認証していない、著者が最終確認。PDF 1・35・36・69 頁を目視 | 事実確認 | native 31 ファイル、変更は `APAL_MANUSCRIPT.tex`・`frontmatter.tex`・`00_introduction.tex`、改名 `12_…` → `20b_…`（我々の差分で同じ）。PDF 70 頁 `22e6df3f` | 受領。**異議なし**。B-2 Step 1 の「著者の最終確認」は新しい著者事項として #236 に数える |
| 229 | abstract の一文（"Two published results enter as named hypotheses: …"）について | 保留（GPT の判定なし）| GPT は「Abstract と Introduction の古典入力の明示を確認した」と書くのみで、**文言の正確さを明示には判定していない**。我々の読み: GS と DPRM は §12 の言うとおり `def … : Prop` で引数として入る（probe: `relation_phase_diagram_all_positive_arity_of_classical : UniformQuadraticSolvabilityOnCodes → DPRM_NN → …`）。TCER は同じ abstract の第 2 段落（"Under a published input on ternary lattice cosets"）と末文（"with the ternary input as an explicit hypothesis"）で別に述べており、"Two" は GS・DPRM に限った数で矛盾しない | 変更なし。異議が出なかったことと、GPT が正確さを積極的に認定したことは区別して記録する |
| 230 | Blueprint: 生成器を独立再実行し 3 ファイル byte 同一。69 ノード（F34・F+H11・M7・D9・R8）、登録ラベル 47 件すべて含む。F/F+H 45 との差 2 は Definition と Remark に別ラベルを与えたため。引用辺は文章の参照関係で kernel 依存グラフではなく、その区別は生成器に明示 | 事実確認 | 我々の再生成も byte 同一。ラベル 47 全在、F 系以外は `Definition 8.4`（D）・`Remark 4.5`（R）。生成器 l.16・84・96 に「cited in」の区別あり | 受領 |
| 231 | ライセンス表示（コード・証明書 MIT、文章 CC BY 4.0）は著者決定として記録。法的意見ではない | 事実確認 | — | 受領 |
| 232 | **新規 P2**: BLUEPRINT.md は「every Lean root の footprint は FinalAxiomReport_current.log にある」と案内するが、登録 74 行・重複除き 72 宣言のうち同ファイルにあるのは 50、22 はない。PaperClaimTypeReport_current.log には 72 すべて。同じ広すぎる説明が §12 冒頭と `TRUST_BOUNDARY_APAL.template.md` にもあり、この二つは R51 から不変（GPT の前回見落とし）。訂正は案内文だけ、証拠不足でも TCER の無条件化でもない。3 ソースへの patch を同梱 | **我々の誤り**（案内文の射程） | `coverage_gate34`: ROWS 74、UNIQUE 72、IN_FAR 50、MISSING 22、IN_PCTR 72。**欠ける 22 名の一覧は GPT の JSON と完全一致**。22 名は `#check` で全解決。例示 3 行は実ログの行と逐語一致。両報告の記録 footprint はすべて標準三公理の部分集合（PCTR 452/452、FAR 417/417 ＋ 依存なし 4）。§12 と TRUST template は R51→R52 で byte 不変（GPT の自己申告どおり）。BLUEPRINT の文は s63 の新規 | **E-34-1。GPT の patch を無修正で受け入れる案**（裁可 R-1）。試走: pkg 3 ソースに適用可、ノード表・DOT 不変、gate5 MA-16（"contained in the standard set" が在る）は保たれ MA-17・18 にも触れない、旧文を固定する道具なし、禁止語・D4 語なし |
| 233 | （GPT の指摘外）TRUST template §1 の表直後の文 "What matters is the last two rows: there is no custom axiom and no compiler-trusting tactic anywhere in the development." | **我々の誤り**（数え違い・射程のつながり） | 表の最後の二行は「禁止トークン 0」と「errors 0」で、文が指すのは下から二・三行目。E-34-1 適用後は直前に「the counts below refer to that report」と入るため、報告の数から開発全体を結論する形になる。主張の中身は真（開発全体のソース走査で 0。監査スクリプトの `forbidden_gate.py` も同種の走査）。この表の最後の三行は置換変数でなく template の固定値「0」 | **E-34-2 候補**（裁可 R-2）。案 A（推奨）: "What matters is the two rows above `errors`: among the reported roots there is no custom axiom and no compiler-trusting tactic." 案 B: 数え違いだけ直し、開発全体の主張は残す。案 C: 触らない |
| 234 | （GPT の指摘外）序論 l.33 "every root's axiom footprint is within the standard three" | 事実確認 | 両報告と RU カウンタ（1542 件、非標準 0）で真。参照先は §12 | 変更しない（gate5・parallel prose に触れず、主張は真）|
| 235 | （GPT の指摘外）README l.111 "every root of the axiom report depends on a subset …" | 事実確認 | 射程が「the axiom report」に限定されている | 変更しない |
| 236 | 新しい課題の数と著者事項の扱い | 事実確認 | **数学 0、文書 1**（#232、3 ソース）＋ 我々の発見 1（#233、同じ template）。著者事項（74 行署名、DOI・REPO、`final` build）は B-2 で「著者の実確認後に記入」「確定 locator 受領後に final build」と、**GPT の審査の待機条件ではなく著者の最終工程**として扱われている。新たに B-2 Step 1「表紙・申告・ライセンス・AI 申告の著者最終確認」が加わった。**Elsevier の declarations tool（.docx）と編集可能な .tex 提出は GPT は触れていない**（我々の submission checklist の 2 項目として残る）| FINAL_RELEASE_ORDER の手順 3 の前に「前付けの事実確認」を一行加える案（R-3 に含める）|
| 237 | B-2 Step 2: 署名書式はこのプロジェクトの手続で、APAL 必須書式だと説明しない | 事実確認 | `AUTHOR_SIGNOFF_SHEET.md` 冒頭は「Gate-14 P02 option A、reviewer が求めた著者点検」と書いており、APAL の要件とは書いていない。core の md/tex に「APAL/Elsevier が署名を要求」の文なし（grep） | 受領。現行のまま |
| 238 | 署名欄 74 行、AUTHOR_REVIEWER・DISPOSITION・SIGNOFF_DATE 各 74 欄空白。EMAIL 設定済、DOI・REPO は UNSET | 事実確認 | 同（count 74・nonblank 0 ×3、locators l.4・5・15） | 受領 |
| 239 | 差分 R51→R52: 657 不変・52 変更・30 追加・15 削除。Lean 326・凍結 59 byte 同一、原 r49 ログ・型証明書・主要証明書・PROOF_COMPANION 同一。Lean manifest 323 行 `db56ee4d…`、原ログ `9ed74140…`。checksum 738/0、core source manifest 396、submission manifest 277 | 事実確認 | すべて一致（facts 12/12）| 受領 |
| 240 | 実行上の限定（container の時間切れで途中中断、署名欄の初回 0 件は区切り文字の仮定違いで再計数） | 事実確認 | 成功件数に中断分を入れていないと明記。最終値は我々の再実行と一致 | 受領。影響なし |
| 241 | 受理見通し 55–70% 据え置き、投稿準備度 98/100、手順書・表紙の修復を数学的意義として上乗せしない | 事実確認（評価） | — | 記録のみ |

**向こうの誤り: 0 件。** 数学上の新しい主張: 0 件（CAS 二系統は既存の主張の再確認）。

## 2. 裁可を仰ぐ事項（Dr. Fukui）

- **R-1**（E-34-1）GPT の `REPORT_SCOPE_R52.patch` を無修正で pkg の 3 ソース（`tools/gen_blueprint.py`、`release/TRUST_BOUNDARY_APAL.template.md`、`submission/native/sections/11_s12_formalization.tex`）に当て、`$W/scripts/gen_blueprint.py` にも同じ変更を入れる。
- **R-2**（E-34-2）TRUST template の "What matters is the last two rows …" を案 A / B / C のどれにするか。
- **R-3** 進め方。GPT は独立の全面再レビューを求めていない。案:
  - (a) **推奨**: r53 を dry run まで作る（Lean 不変 → r49_fresh を `MPUP_LEAN_UNCHANGED=1` で流用、§12 変更に伴い MD・PROOF_COMPANION・STATEMENT_MAP_FULL・FIGURES を作り直し、parallel prose の上限を測り直し、SEAL_WHAT_IS_OPEN を書き直す）。封緘と GPT への送付はしないか、するかを先生が決める。その後 FINAL_RELEASE_ORDER の著者手順へ（手順 3 の前に「前付けの事実確認」を追加）。
  - (b) r53 を封緘して GPT に短い確認として送る（GPT は不要としているが、確認を得る道）。
  - (c) 訂正を著者の `final` build のときにだけ入れる（途中の dry run なし）。§12 は PDF・MD に波及するため、推奨しない。

## 3. 裁可（2026-09-30 14:17、Dr. Fukui「あなたの推奨で」）

- **R-1 = 採用**: E-34-1 は GPT `REPORT_SCOPE_R52.patch` を無修正で pkg 3 ソースに当て、`$W/scripts/gen_blueprint.py` を同期する。
- **R-2 = 案 A**: TRUST template の一文を "What matters is the two rows above `errors`: among the reported roots there is no custom axiom and no compiler-trusting tactic." にする。
- **R-3 = (a)**: r53 を dry run まで作る。封緘・GPT への送付・公開・投稿は先生の専決のまま（同じ指示の中で「私の承認が不要なものをどんどん進めて。理想は、GPTの宿題を全部終わらせること」）。

## 4. 実施（s64、裁可後）

- E-34-1: GPT patch を pkg 3 ソースに無修正で適用（gen_blueprint f872af4f → 12f26bd8 = 試走、TRUST template 33086118 →（E-34-2 と合わせて）4ed37032、§12 12c533ee → 7632ef8d = 試走）。`$W/scripts/gen_blueprint.py` = pkg。事前に gate5・parallel_prose・generate_trust・paper_claims_check・全 tools を grep、旧文・新文とも固定なし。
- E-34-2: 案 A を TRUST template に適用（gate5 の TRUST 向け門 MA-9/11/28/30/61/64、MB-4、ME-12、MH-1…11 と照合、抵触なし）。
- 文書: `SEAL_WHAT_IS_OPEN.md` を r53 の内容に書き直し（f4a47176、一文ずつ真偽を点検）。vault に `ERRATA_R53_20260930.md`、`GATE34_CHECKLIST.md`（task 1 DONE、task 2 PARTIAL = 著者の工程のみ）、`LETTER_GATE34.md`（template は `s64_evidence/r53/LETTER_GATE34.template.md`）。
- `r53/prepare_r53.py`（602d04a0 の複製）: GATE34 一式・cas_s64 9 点・README_r53・assemble_r53.sh（f2de2bca から）・SEAL_INPUT（r53 / session_64 / 0.31.0 / LETTER_GATE34 / RELEASE_DATE 2026-09-30）・CITATION（0.31.0、date-released 2026-09-30）。
- dry run 1: EXIT 1 PARALLEL_PROSE（GATE31 E 47 > 46、§12 の位相ずれ。GATE34 E 16 は未宣言）→ `r53/patch_parallel_prose_s64.py`（写しで試走 → 実物、両写し 4938d951）。
- dry run 2: EXIT 1 BLUEPRINT_DETERMINISM（BASE r52 の `dep_graph.pdf` が第一回生成の出力先に残り、第二回の空ディレクトリと食い違い）→ assemble_r53.sh 7c-bis の生成前に `rm -rf "$OUT/papers/blueprint"`（7c5bf2fb）。
- dry run 3: **EXIT 0**。gate5 363/FAIL 0、paper claims 47/0、16/16、6/6、parallel prose OK、destroyer 0、Blueprint 決定性 OK、PDF 70、SHIPPING_ARTIFACT_GATE OK、PACKAGE_FILES 1569。BASE との差: 変更 34・追加 22・削除 2（SEAL_r52・assemble_r52 は history へ）。`lean/` 326・`frozen_statements/` 59 byte 同一。MD は §12 の一段落のみ、PDF は語単位で §12 の一段落のみ（以降は行番号が 1 ずれるだけ）。PROOF_COMPANION・STATEMENT_MAP_FULL は r53 の源から作り直して shipped と byte 同一、FIGURES は TRUST_FIGURES_MISMATCH=0。
- split 予行 1: core 746、SHA256SUMS 745 OK、CLEANROOM_REFERENCE=ok、CORE_SHIPPING_EXIT=0、3/3、8/8、16/16、6/6、core のログ = r49 cold room。書簡を実抜粋で再記入。
- 我々の誤り: `<(...)` を二度（どちらも構文エラーで何も走らず、やり直し）。

## 5. 公開へ（2026-09-30 14:56 Dr. Fukui「github zenodoにアップしよう」、15:00 の回答）

- 署名シート: 「署名シート確認した。記入はあなたが代理でやって進めて。」→ `publish/fill_signoff_s64.py` で 74 行 × 3 欄を記入（AUTHOR_REVIEWER=Hiroki Fukui、DATE 2026-09-30、ASSISTED_BY=Claude のまま）。AUTHOR_DISPOSITION は著者承認済みの Layer-2 判定の書き写し: EXACT 系 72 行 → MATCH、row 23（Theorem 8.5 の第二の根、COROLLARY）→ MATCH VIA 第一の根、row 60（Lemma 10.3、PARTIAL-EXACT）→ MATCH VIA rat_discriminant_of_total'。最初の試行で正規表現が改行を食い見出しを連結したため、バックアップから戻してやり直した（差分 222 行 = 74 × 3 のみ）。
- 前付け: 再確認を求め、修正の指示なし（「No preference」）。事実の認証はしていないと記録。
- リポジトリ名: 指定なし → 推奨の `single-quadratic-definability`。
- Zenodo 下書き（API、未公開）: software 23053094 = DOI 10.5281/zenodo.23053094、paper 23053096 = DOI 10.5281/zenodo.23053096（`publish/zenodo_drafts_s64.json`）。
- locators: DOI = https://doi.org/10.5281/zenodo.23053094（software）、REPO = https://github.com/hirokifukui/single-quadratic-definability。CITATION.cff に repository-code と doi を追加。SEAL_WHAT_IS_OPEN の末段、書簡 §5、チェックリスト task 2（DONE）、正誤表末段を最終状態に合わせて改稿。
- final dry run 1: EXIT 0（mode=final、PLACEHOLDER_GATE OK、overfull>5pt 0、PDF 70、SIGNOFF_CARRIED 74 / BLANK 0、gate5 FAIL 0）。
