# R52 実行記録

入力：`APAL_PUBLIC_CORE_mpup_gpt_r52_20260928.zip`。ZIP SHA-256 `bec8319637757380ca63af73d54e9f0b8eb612f6893772db2a07829e29a26a5b`。添付splitのcore行と一致。history archiveは未受領・未検査。

## 保存した証拠

- `evidence/independent_findings.json`：独立hash検査、差分、原ログ同一性、manifest再列挙、Blueprint再生成一致、署名欄数。
- `evidence/diff_inventory.json`：R51→R52の全ファイル差分。657不変、52変更、30追加、15削除。AI節の改名を含む。
- `evidence/blueprint_report_coverage.json`：74登録行、72異なる宣言、FinalAxiomReport50／PaperClaimTypeReport72、欠けた22宣言の正確なリスト。
- `evidence/execution.json`：実際に成功した著者検査器・generatorの各command、cwd、exit、秒数。ログは同ディレクトリ。
- `evidence/patch_dry_run.log`：原提出物ではないコピーに対するpatch適用可能性。
- `evidence/patched_blueprint_regeneration.log`：提案generatorを別出力に実行。ノード表・DOTは原版と不変。

## 実行上の限定

最初のsession型container呼出はサポートされず、実行されなかった。通常execへ切り替えた。一度の複数テスト実行はcontainer時間制限で中断された。保存された成功ログがない途中経過は成功件数に含めず、その後個別再実行した。signoffは最終の個別実行が6/6・exit0。

独立検査の署名欄カウントは最初、区切りをcolonと仮定して0件を返した。実ファイルを読んで`^AUTHOR_...=`へ直し、各74行・非空0を確認した。初回の0件を著者データの欠落とは扱っていない。

レンダリング：PDF1–2、35–36、69頁。目視：1、35、36、69頁。全70頁の再目視、PDF再組版ではない。描画に使ったフォントファイルを配布していない。

未実施：Lean/lake独立ビルド、Sage、GitHub Actions実走、PDF再組版、実locatorによるfinal build、オンライン新規性・雑誌規程の再調査。添付資料の刊行物への言及を、今回自ら再照合したものとして扱っていない。

提出物の元ZIPと展開したR52参照ツリーには修正patchを適用していない。提案patchは別コピーでテストした。著者の全体ビルド・新しい配布物の再封緘は行っていない。
