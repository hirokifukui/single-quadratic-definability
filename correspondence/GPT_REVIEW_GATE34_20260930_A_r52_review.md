# APAL R52 増分・最終化レビュー

## 結論

**R51で要求した3課題は3/3合格。数学の凍結を維持し、技術的な投稿候補として受け入れる。今回の監査範囲で、新しい数学的P0、ビルド失敗や証拠欠落に相当するP1は見つけていない。**

新規の軽微な訂正は一件。公理レポートの対象範囲を「全root」とする説明を、実際の報告ファイルへ合わせる。新しいBlueprint、既存の§12、trust templateに同じ説明がある。これはP2の証拠案内文の訂正であり、証明・宣言・外部入力の修正でも、記録の未同梱でもない。添付の3ソースへのpatchを最終生成時に取り込めばよい。この訂正のために新しい数学ラウンドや独立した全体再レビューを要求しない。

本レビューは添付R52 coreとR51 coreの差分、現在の証拠・手順、追加資料の監査である。過去に読んだ全証明をあらためて逐行審査したものではない。Lean/lakeは現在の環境になく、独立kernel再ビルドは行っていない。原ログは著者のR49/agora実行の保存記録であり、今回のGPT実行ではない。

## 1. 定理・工程の評価

| 対象 | R52評価 | 範囲 |
|---|---:|---|
| II-D：鋭い次元非圧縮 | 100%維持 | 既存のTCER不要の経路、ソース監査上の評価 |
| 一般full NF、多出力分類、scalar三族分類 | 100%維持・条件付き | TCERからの含意。TCERを証明したことにしない |
| 零証人分類・床関数の最小証人数1 | 100%維持 | TCER不要 |
| 別表示の一意証人化 | 100%維持・条件付き | TCERからの含意。元の任意表示の一意性ではない |
| TCER本体のLean証明 | 0%維持 | 当該命題本体の証明は未実装という従来評価 |
| 通常数学の証明説明 | 98/100据え置き | 新しい証明の追加・再検証なし |
| 投稿準備度 | 98/100 | 著者最終確認・実locator・final生成を残す |
| 前回3課題の完全合格率 | 3/3 = 100% | 新規P2とは分離 |

100%は指定された仮定・結論・接続についての従来のソース監査評価を維持するという意味であり、正しさの確率でも独立kernel認証でもない。工程指数98/100は残り作業時間の2%を意味しない。受理見通しは前回の主観的55–70%を据え置くが、今回、新規性・雑誌の実測統計・外部研究を再調査して較正してはいない。手順書や表紙の修復を数学的意義の増大として確率へ上乗せしない。

## 2. 前回の3課題

### 1：手動ビルド — 合格

`release/README_BUILD_APAL.template.md`と生成済みREADMEは、default target MPUP、DiophCompression、ResearchUpgradeの三段階を含む。`lean/lakefile.lean`・`lean/fresh_build.sh`・保存原ログとの対応を確認した。前回指摘したRUだけでなく、著者が追加で確認したMPUPの依存も同じ修正で覆われる。今回の環境で実ビルドしたとは数えない。

### 2：再生成・配布証拠 — 合格

実際に受領した最終ZIPを展開して検査した。チェックリストに残るPARTIALは封緘前の記録であり、現在の最終ZIP検査成功によって合格へ更新する。

Lean 326ファイルと凍結声明59ファイルはR51とbyte同一。原R49ビルドログ、型証明書、主要な証明書とPROOF_COMPANIONも同一。Lean manifestは独立列挙した323項目と同梱一覧がbyte同一で、hashは `db56ee4d1708c2e348f9412c282a093b22b5302b97b992fae3b03ad6ec1c2e7b`。原ログhashは `9ed741407611c68f187b475d3cbc48b0f6b62a2a06a8ef83376f3cd195307ff9`。

一方、本文・PDFはbyte同一ではない。これは下記の著者決定として列挙された変更による。数学不変と本文バイト不変を区別する。

### 3：著者へ返却 — 合格

数学を増やさず、著者署名・locator・final build・未公開状態を別々に記載している。現在の署名シートは74行で、AUTHOR_REVIEWER、AUTHOR_DISPOSITION、AUTHOR_SIGNOFF_DATEは各74欄とも空白。EMAILは今回設定されたが、DOIとREPOはUNSET。今回、外部公開・予約・投稿・署名の代行は行っていない。

## 3. 追加変更の扱い

### 本文と著者情報

nativeは31ファイルのままだが、frontmatter、Introduction、master TeXが変わり、AI宣言節が同文のまま改名・移動した。表紙の所属・メール・Funding・利益相反申告、AbstractとIntroductionの古典入力の明示、AI宣言の参考文献直前への移動を確認した。主要数学節、登録声明、証明ノートを再設計した変更ではない。

R52のレター・dispositionでは、これらは著者の別途決定として記録されている。その記録に基づいて区別し、GPTの前回課題の範囲外だったこと自体を違反とは扱わない。所属・Funding・利益相反の事実を外部照会で認証したわけではない。著者が最終確認する。

PDFは70頁。今回レンダリングし目視したのは1、35、36、69頁。表紙、外部入力表、AI宣言の参考文献直前への配置を確認した。2頁もレンダリングしたが、全70頁を今回再目視したとは主張しない。PDF再組版はしていない。

### CI

新しいworkflowは三ライブラリをbuildし、DCとRUのauditを別stepで呼ぶ。working-directoryはlean、ログのupload pathはlean配下。shell: bashとpipefailを意識した構成になっている。これはソースの静的確認であり、GitHub実行成功の認定ではない。著者も未実行と明記している。公開時に`.github/workflows/`へ置く作業は別である。

### Blueprint

生成器を独立に再実行し、BLUEPRINT.md、blueprint_nodes.tsv、dep_graph.dotの三ファイルが配布版とbyte同一であることを確認。69ノード、F34、F+H11、M7、D9、R8。47件のregistry labelがすべて含まれる。F/F+Hの45件との差2件は、DefinitionとRemarkに別ラベルを与えたためで、脱落ではない。

引用辺は文章の参照関係であって、kernel依存グラフではない。その区別はgeneratorに明示されている。循環や省略があることだけで数学的循環証明とは扱わない。生成一致は内容の真偽の証明でもない。

コード・証明書MIT、文章CC BY 4.0という表示は今回の著者決定として記録されている。本レビューは法的な権利処理の意見書ではない。

## 4. 新規P2一件：公理レポートの対象範囲

`papers/blueprint/BLUEPRINT.md`は「every Lean rootのfootprintはFinalAxiomReport_current.logにある」と案内している。しかし、登録済み74行のうち重複を除いた72宣言について、同ファイルで確認できるのは50、残り22は載っていない。一方、`PaperClaimTypeReport_current.log`には72宣言すべてについて型とaxioms欄がある。

例：`sealedFullNF_of_TCER`、`scalar_singleQuadratic_iff_of_TCER`、`floorThird_min_witnesses`は後者に記録されている。

同じ広すぎる説明が、既存の§12冒頭と`TRUST_BOUNDARY_APAL.template.md`にもある。§12とtemplateのこの文章はR51から不変であり、前回私が見落としていたもの。Claudeが新しく証明を壊した、または既に指摘された修正を再度無視したという扱いにはしない。

訂正内容は「FinalAxiomReportはその列挙rootの報告」「登録されたpaper宣言の型・footprintはPaperClaimTypeReportで確認する」とするだけ。現在ある証拠が足りないという指摘ではない。TCERの含意を無条件化したという指摘でもない。新たなLean実装や公理レポートの再生成は不要。

`REPORT_SCOPE_R52.patch`はgenerator、trust template、native §12の3ソースだけへの提案。原R52には未適用。別コピーでdry-run成功。修正版generatorを別出力へ実行し、ノード表とDOTグラフはbyte不変、Blueprintの案内だけが変わることを確認した。本文PDFとtrust文書は著者側の通常の最終生成に含めて同期する。既存の検査値を新しい主張に合わせて捏造・手書きしない。

## 5. 独立実行と未実施

| 検査 | 結果 | 性質 |
|---|---:|---|
| ZIP CRC / split記載のcore hash | 一致 | 独立検査 |
| checksum | 738件、不一致0 | 独立hash実装 |
| core source manifest | 396件、不一致0 | 独立hash実装 |
| submission manifest | 277件、不一致0 | 独立hash実装 |
| Lean manifest | 323件、同一hash | 独立列挙 |
| core verify | exit0 | 著者検査器の再実行 |
| cleanroom対照 | 3/3 | 著者検査器の再実行 |
| checksum対照 | 8/8 | 同上 |
| paper claims | 47件、FAIL0 | 同上 |
| paper-claim負対照 | 16/16 | 同上 |
| signoff対照 | 6/6 | 合成署名の対照。実署名ではない |
| frozen statement diff | theorem1092/1092、definition298/298、FAIL0 | 著者検査器の再実行 |
| SymPy | 17/17、負対照6/6 | 著者スクリプトの再実行、一般証明ではない |
| Blueprint再生成 | 3ファイルbyte一致 | 著者generatorの再実行 |

未実施：独立Lean/lakeビルド、Sage実行、GitHub CI、PDF再組版、実locatorによるfinal build、history ZIPの検査、外部文献・新規性・所属・雑誌規程の再調査。

最初の複数コマンド実行はcontainer側の時間制限で中断された。その後、個別に実行して上表の結果を得た。特にsignoffの最初の中断を成功として数えていない。最終の個別再実行は6/6で終了0。

## 6. 終了判断

通常の重大修正レビューとしては終了。既存数学と登録声明の再審査を次の必須工程にしない。残すのは上記P2の案内文同期と、著者が決める正確な所属・申告・署名・公開locator・final生成である。

TCER本体の再形式化、第二環境のビルド、新たな数学、Blueprintの証明依存DAG化を待機条件に追加しない。P2の訂正が最終生成に入ったら、現在の正しい検査を一度実行し、著者が公開・投稿を判断できる候補として返す。未発行DOIを推測したり、74行を機械的に代署したりしない。
