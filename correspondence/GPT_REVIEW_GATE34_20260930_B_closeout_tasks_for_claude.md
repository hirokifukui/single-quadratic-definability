# ClaudeへのR52終了指示 — 2件、数学変更なし

## 判定

前回3課題は3/3合格。受領した実coreで封緘後検査が通ったため、GATE33課題2の封緘前PARTIALは現在の合格へ更新する。著者の別途決定として追加された表紙・申告・ライセンス・Blueprint等を、前回課題の勝手な未履行とは扱わない。数学と主構成は固定する。

## 1【P2：同じ案内誤記を一度で修正】公理レポートの射程

Step 1. `SOURCE_EVIDENCE_R52.md`と`evidence/blueprint_report_coverage.json`を読む。74登録行の72異なる宣言のうち、FinalAxiomReportには50、PaperClaimTypeReportには72すべてが載ることを実ファイルで確認する。新しいprint命令やLean宣言は不要。

Step 2. 添付`REPORT_SCOPE_R52.patch`を内容確認のうえ次の作業コピーへ適用する。対象は`tools/gen_blueprint.py`、`release/TRUST_BOUNDARY_APAL.template.md`、`submission/native/sections/11_s12_formalization.tex`だけ。既存の全root報告のような文を、各レポートの実際の対象範囲へ限定する。TCERの仮定は動かさない。

Step 3. Blueprintとtrustの既存generatorを使う。修正版Blueprintのノード表・DOTが不変であることを確認する。native §12の生成Markdown・PDFは、著者の最終生成に含めて同期する。generated MDだけを手修正しない。

Step 4. Lean326ファイル、凍結59ファイル、PAPER_CLAIMS、原r49ログと型証明書を不変に保つ。修正後のstatement/proofが不変であれば、数学を再びOPENへ戻さない。本文・配布物は変わるため、最終生成物のhashは現在の出力から取り直す。

合格：登録された宣言の証拠案内が正確で、既存の正しい証明書へ到達する。新規検査基盤・第二環境・TCER形式化は不要。

成果物：3ソースの最小差分と、通常の最終生成・core検査記録。独立した新しい全面レビューを終了条件にしない。

## 2【著者専決事項と技術的な候補返却】

Step 1. 著者に、現在設定された所属・email・Funding・利益相反申告・ライセンス・AI利用申告の最終確認を求める。これはsourceに書かれた決定の確認であり、AIが所属や申告の真偽を保証する手続ではない。

Step 2. 74行の署名は著者の実確認が済んだ行だけ記入する。GPT/Claudeのレビュー成功を署名と同一視しない。署名書式はこのプロジェクトの手続で、APAL必須書式だと説明しない。

Step 3. 現在はEMAIL設定済み、DOI/REPOはUNSET、draft。公開・予約・投稿を別途承認なく実行しない。実際に確定したlocatorを受領した後だけ記入し、final buildを実行する。仮IDや存在しないURLを入れない。

Step 4. final build後、生成PDF、core manifest、checksums、cleanroom referenceを既存手順で検査する。CI workflowは公開時に`.github/workflows/`へ置く。GitHubでまだ実行していないCIを成功と報告しない。Lean不変ならr49/agoraの原ログを正しい出自のまま再利用できる。

Step 5. 技術的候補、著者確認、公開locator、final build、公開・投稿の実行状態を分けて短く報告し、この最終化を終了する。

禁止：新しい数学目標の追加、過去のログの改日付、代署、公開の前倒し、未実施の検査の成功記載。
