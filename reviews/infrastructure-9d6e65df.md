# 原稿以外のレビュー（sunaemon/math-private @ 9d6e65df）

対象リビジョン: `9d6e65df`（2026-10-29 時点の main HEAD）

## 範囲と方法

- 対象: リポジトリ全1,354ファイルのうち、原稿（日英・抜粋版の本文 Markdown）と内容データを除く **222ファイル（約1.6MB）**。内訳は tools/（Haskell フィルタ、Python ツール群、formalization viewer、Pandoc テンプレート）、tests/、CI（.github）、setup.sh、Makefile、mise 設定、lefthook・lint 設定、AGENTS.md・README 等の文書、.claude/.codex のスキル定義、polish-space/tex のマクロ層。
- 除外: 本文 Markdown、Lean 証明そのもの（904ファイル）、PO/POT カタログ（翻訳内容）、references.bib（2026-10-28 に照合済み）、tools/formalization-viewer/vendor/ の第三者コード、フォント・wasm 等のバイナリ。
- 方法: 領域別10バッチ（F1/F2 フィルタ、P1/P2 Python、V1/V2 ビューア、B1 ビルド・CI、T1 テスト、D1 文書、X1 TeX 層）に分けて通読し、指摘はファイル・行に紐付けた。主要な指摘数件は統合時に原典で再確認した（AGENTS.md の symlink 記述、setup.sh の rm -rf、viewer の safeHref、sourcemap の span_json はいずれも原文どおりであることを確認済み）。

## 総評

**重大な脆弱性も明白なバグも見つからなかった。** フィルタ本体（Main.hs 全4,164行）を通読しても明白なバグはなく、ビューアのサーバ側もループバック限定バインド、Host/Origin 検査、allowlist＋realpath 再検査、make ターゲットへのインジェクション対策（正規表現検証＋テスト付き）まで意図的に設計されている。CI はアクションを SHA でピン留めし権限最小、Codex 向け setup はダウンロードに SHA256 ロック、LaTeX ロックは stale 回収と pid 再利用対策まで含む原子的な実装で、コメントによる設計判断の明示が全体に一貫している。水準は高い。

指摘は合計 **182件**（バッチ178件＋統合担当分4件）。中心は次の3つの積み残しで、いずれも「壊れている」ではなく「育ったリポジトリの手入れ」である。

1. **文書ドリフト（D1、25件）** — AGENTS.md・README・スキルの記述が実装や現状からずれている。特に AGENTS.md はこのリポジトリで作業する AI エージェントへの指示書そのものなので、記述の誤りがそのまま作業の誤りになる。
2. **性能の積み残し（P1、F1、X1 ほか）** — 「ビルドが重い」の内訳の一部はここにある。sourcemap 生成の再走査、フィルタの引用ごとのプロセス起動、使われていない TikZ ライブラリの全パス読み込み。
3. **テストの穴（T1 25件、F2 ほか）** — 依存グラフの収集セマンティクス（辺の向き・集計・章帰属）を検証するテストがなく、ビューアのセキュリティ境界にも単体テストがない。テスト側にも固定名一時ディレクトリの並行干渉など壊れやすさがある。

## 優先度の高い指摘

### 文書・指示の不整合（最優先: エージェントの作業指示に直結）

- **D1（AGENTS.md:52）**: 「The untranslated Japanese-book chapters are symlinks to their English sources」とあるが、l10n/README は「no chapter falls back to an English-source symlink」と正反対で、実態（全41ファイルに日本語本文）とも l10n 側が一致する。同じ節の "pilot" という位置づけも現状（全章翻訳済み・校閲2巡完了）から古い。viewer README にも同じ古い前提が残る。
- **D1**: ルート README の Codex 開始指示「Use chapter previews for PDF checks」が AGENTS.md の「プレビューを routine verification に使うな」と衝突。book-build スキルの既定（リリース PDF をバックグラウンド開始）も AGENTS.md の TeX-only 方針と衝突したまま。
- **D1**: book-section-review スキルが .codex と .claude で全面ドリフト（xhigh 本体実行 vs Sonnet 委譲＋make 禁止）。同名スキルの正本が不明で、どちらで作業したかで手順が変わる。

### 性能

- **P1-1/P1-2**: `booklink_sourcemap.py` の `span_json` が呼び出しごとに全文の行オフセット表を再構築し、`attach_tex_matches` 経由ではエントリごとに生成 .tex 全文（数MB）を再走査する。章テキストの再読込と statement 解析も Lean ファイル・マーカー単位で繰り返される。
- **F1**: フィルタが引用ごとに pandoc プロセスを起動する箇所と、`breakRawMath` の二乗オーダーの蓄積。全書走査の回数も多い。
- **X1-1（中）**: TikZ の `graphs`/`graphdrawing`/`fit` と `\usegdlibrary{force}` が全パスで読み込まれるが、依存グラフのレイアウトは Haskell 側で計算済みで TeX 側は座標固定の素の tikzpicture のみ。実使用は `backgrounds` だけだった。

### 安全性・堅牢性

- **B1-2**: setup.sh の `rm -rf` 対象（`TEXLIVE_INSTALL_ROOT`、`PERL_LOCAL_LIB`）が環境変数で上書き可能で、リポジトリ配下であることの包含ガードがない。既定値は安全だが、上書きした環境変数が広いパスを指すとそのまま消す。
- **B1-1（中）**: setup.sh の dry-run が、システムに cpanm がある環境では Perl モジュール未導入時に exit 1 する。「dry-run は副作用も失敗もしない」という前提が崩れる。
- **B1-9（中）**: .github/workflows/check.yml に `timeout-minutes` がなく、既定の360分まで走りうる。
- **V1**: PDF リンク注釈の URL が `pdf.ts:322` で `box.href = annotation.url` と未検証のまま href 化される。他所では `safeHref` を経由する設計なのに、ここだけ素通り（PDF 内リンクは外部由来になりうる）。
- **V2**: manifest の `dir` が未検証（`lspDir` 側の検証と非対称）、static-dist の `--dist` 再帰削除にガードなし。lean-bridge の spawn 失敗時に固まる可能性、initialize restart の直列化欠如による孤児 Lean プロセスの可能性はいずれも「要確認」。
- **X1-2（中）**: `\SkipStart` が素の `\hypertarget` で、同ファイル自身が詳述する垂直モードの1行ずれ対策（`\booklinkanchorhere`）を skip アンカーだけ受けていない。

### 正しさ（要確認を含む）

- **P1-3/P1-4**: `find_next_decl` が `partial def` / `protected theorem` 等を見落として後続の宣言へマーカーを誤結合しうる。`find_decl_end_line` は宣言内部の空行で打ち切られる。全マーカー unresolved の章が coverage レポートから丸ごと消える（P1-11）点も、無言の欠落として要注視。
- **F2**: 依存グラフレイアウトのキャッシュ署名がレイアウト定数の大半をカバーせず手写しリテラル（1218–1231行）。辺の上位18件への無言の切り捨て（154行）。`\part{` の部分文字列検出（275行）。行高さ [0,1] のハードコードは7部以上で静かに重なる（496行）— 現行は5部制なので顕在化していない。キャッシュパースが NaN/Infinity を受理する（1315–1319行）。
- **P1-7**: `formalization:` 注釈の文法が3実装（sourcemap / coverage / books_mk）に分散し、範囲と理由文字列の解釈が食い違う。文法の正本を1か所に寄せるのが望ましい（books_mk.py 側の正規表現は私も確認済みで、解釈の分岐は実在する）。

### テスト

- **T1（25件）/ F2**: 依存グラフの収集セマンティクスを検証するテストがない。ゴールデンテストの成功ケースも終了コードのみで回帰を検出できない。テスト側の壊れやすさ（固定名一時ディレクトリの並行実行干渉、pandoc/diff 不在時の例外化）や、実装ロジックの複製・自己参照も複数。
- **V2**: セキュリティ境界である `isAllowedPath` / `applyMount` に単体テストがない（projects.test.ts は1件のみ）。

## 統合担当分（Makefile と小物ツール、私が直接読んだ範囲）

- **M-1**: リリース PDF ルールが補助ファイルを削除してから固定3パスで組む点と、`LATEX_LOCK` が全 TeX 実行をリポジトリ全体で直列化する点は、ビルド速度の相談の際に既出（設計としての清潔さと引き換えの選択であり、ここでは欠陥として数えない）。
- **M-2**: PDF ターゲットが `Makefile` 自体に依存するため、Makefile を触るたびに全書が再ビルドされる。依存に版数スタンプ等を挟む手はあるが、現状でも実害は「待ち時間」にとどまる。
- **M-3**: `books_mk.py` は make 起動ごとに全章の全文を読んで formalization-skip 注釈を走査する（2書で約5.5MB）。実測上の問題にはなりにくいが、マニフェストに持たせれば消える走査ではある。
- **M-4**: `latex_lock.py` には保持中の heartbeat がなく、1時間を超える正当な保持でも max-age で stale 回収されうる。コメントで認識済みの割り切りで、単一パスが1時間を超えることは通常ないため実害は低い。
- **M-5（要確認）**: ルート README の Codex 節に「without installing Pandoc 3.9.0.2」と旧い版数らしき記述がある（mise.toml の現行ピンは 3.12.1）。Codex プロファイルが使うシステム Pandoc の版を指すなら誤りではないが、読み手には判別できない。
- 良い点として確認したもの: `refresh_debug_pdf.py` の収束駆動（aux のバイト比較と .idx の sha256 で再実行を決める）、`enable_booklink_highlight.py` の冪等性と失敗時の loud な終了、`book_manifest.py` の型検証、`SectionRef.hs` の単一トークナイザ化（走査器のドリフト防止）、mise.toml の全面ピン留めと理由コメント、.gitignore の「自前ツール生成物だけを書く」方針明記。

## 領域別サマリ

| バッチ | 領域 | 件数 | 主な中身 |
|---|---|---|---|
| F1 | book-filter/Main.hs | 12 | 明白なバグなし。性能3件、用語アンカー slug 衝突の未検出、Emph だけ allowLinks=False の非対称など |
| F2 | DependencyGraph.hs・SectionRef.hs・ゴールデンテスト | 9 | レイアウトキャッシュ署名の漏れ、辺の無言の切り捨て、グラフ収集セマンティクスのテスト不在。SectionRef と cabal 定義は指摘なし |
| P1 | booklink 系 Python | 21 | span_json の再走査（性能）、宣言検出の取りこぼし（要確認）、formalization 注釈文法の3実装分散 |
| P2 | 翻訳チェック・ビルド検証 Python | 20 | 中7件・低13件。チェックの検出漏れ・誤検出、ツール間の重複 |
| V1 | ビューア（クライアント） | 17 | 注釈 URL の safeHref 未経由、loadingTask 破棄漏れ、localStorage 無防備、存在しない要素への死んだ配線、app.ts 2,715行の巨大さ、a11y 3件 |
| V2 | ビューア（サーバ・e2e） | 22 | manifest dir 未検証、プロセス管理の要確認複数、検証ロジックの重複実装、セキュリティ境界のテスト不足。重大な脆弱性はなし |
| B1 | setup・CI・設定 | 16 | dry-run の exit 1、rm -rf のガードなし、CI タイムアウト未設定、devcontainer の浮動タグ |
| T1 | tests/ | 25 | カバレッジの穴6件、壊れやすさ10件、実装の複製・自己参照4件、保守性5件 |
| D1 | AGENTS.md・スキル・README 群 | 25 | 不整合・古い記述9件、.claude/.codex ドリフト6件、付随スクリプト6件、冗長4件 |
| X1 | TeX マクロ・テンプレート層 | 11 | TikZ ライブラリの無駄な全パス読み込み、\SkipStart のアンカー対策漏れ、font-settings フォークのドリフト検出なし。JA の macros は symlink で複製なし、マクロ定義454件に重複なし |

以下、各バッチの全指摘をそのまま収録する。


---

# 付録: バッチ F1

# コードレビュー バッチF1（sunaemon/math-private @ 9d6e65df）

対象: `tools/book-filter/Main.hs`（ローカルコピー `private/infra/tools__book-filter__Main.hs`、全4,164行を通読）。補助参照: `SectionRef.hs`、`tests/run-book-filter-golden.hs`、`tools/booklink_sourcemap.py` の該当箇所。観点は正しさ・保守性・性能・コメントとの整合で、原稿本文の内容は対象外。著者がコメントで意図を明記している設計（ゲートの保守的な広さ、`\\%` の扱い、行ベース走査の線形化など）は指摘に含めていない。

総評: 全体に境界条件への配慮と意図のコメントが厚く、明白なバグは見つからなかった。以下の12件は、性能の非対称性、暗黙の形式依存、照合の緩さなど、確度に差のある指摘である（断定できないものは「要確認」と明記）。

## 1. 引用候補ごとに pandoc サブプロセスを起動し、キャッシュがない

- 場所: `tools__book-filter__Main.hs:1203` / `parseRawCitation candidate = do pandoc <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"; (code, out, err) <- readProcessWithExitCode pandoc...`
- 問題点: `rawCitationInlines`（1123行）が `@` を含む角括弧候補のたびに `parseRawCitation` を呼び、その都度 pandoc を新規プロセスとして起動する。Raw TeX の定理・証明環境には引用が多数あり、同一文献への同一形式の引用が繰り返されても毎回プロセス起動（概ね数十〜数百ms級）が発生する。全書では数百回規模になりうる。要確認（実際の候補数は原稿依存）。
- 提案: 候補文字列をキーにしたメモ化（`IORef (Map Text (Maybe Inline))`）を挟む。同一候補の再解析を消すだけでも効果がある。さらに進めるなら、候補をまとめて1回の pandoc 呼び出しで解析する。

## 2. `readIndexGlossary` だけ pandoc の解決方法が異なる／デコードエラーが捨てられる

- 場所: `tools__book-filter__Main.hs:992` / `(code, out, err) <- readProcessWithExitCode "pandoc" ["-f", "markdown", "-t", "json"]...`、および 1002–1005行の `_ -> ioError (userError ("book-filter: cannot read index glossary: " <> err))`
- 問題点: (a) `parseRawCitation` は `PANDOC_BIN` 環境変数を尊重するのに、こちらは PATH 上の `"pandoc"` 固定。mise 管理の環境では、PATH の pandoc が不在（用語集読み込みだけ失敗）または別バージョン（フィルタ本体と異なる解析結果）になりうる。(b) 終了コード成功でも JSON デコードに失敗した場合、実際のデコードエラーではなく pandoc の stderr（通常は空）がエラーメッセージになり、原因が追えない。
- 提案: pandoc バイナリ解決を共通ヘルパーに揃え、デコード失敗時は `Left errMessage` の内容をメッセージに含める。

## 3. ソースマップの行ベース手製 JSON パーサが、発行側の整形形式に暗黙依存している

- 場所: `tools__book-filter__Main.hs:2046`（`parseBooklinkSourceMap`）、`2231`（`parseSkipInjections`）/ 終端判定 `T.strip line == "}," || T.strip line == "}"`（2086、2250行付近）
- 問題点: 両パーサとも「1キー1行」「オブジェクト終端は単独の `}` / `},` 行」「`"match"` の値は平坦」という `json.dumps` の pretty-print 形式を前提にしている。`match` の中に将来入れ子オブジェクトが増えると、その閉じ行でエントリが早期終了し、後続フィールド（source や offsets）を読み落としたまま黙って欠落する（`finishPending` が不完全なエントリを捨てるため、エラーにもならない）。一方で Aeson（`eitherDecode`）は既に依存にあり、同ファイル内でも使われている。
- 提案: 配列部分は Aeson で構造として解析し（エントリ順序は現行どおり保持できる）、行パーサは置き換える。置き換えが難しければ、少なくとも「想定形式から外れたら黙って捨てずに失敗する」検証を足す。

## 4. `breakRawMath` が1文字ずつの蓄積で数式長に対して二乗

- 場所: `tools__book-filter__Main.hs:3078` / `go (acc <> "\\$") (T.drop 2 txt)`、`let (prefix, rest) = T.splitAt 1 txt in go (acc <> prefix) rest`
- 問題点: `acc <> 1文字` の繰り返しは蓄積テキストを毎回コピーするため、数式セグメント長 n に対して O(n²)。`$$...$$` や `\[...\]` の長い display 数式（aligned 等）を含む Raw ブロックで効く。同ファイルの他の走査（`linkRawLatexMath` のチャンク化、`breakLatexComment`）は「線形化した」とコメント付きで対策済みなのに、ここだけ旧来のパターンが残っている。同種の蓄積は `takeBalancedArg`（2793行、`T.snoc` の逐次追加）と `balancedDelimited`（3979行）にもあり、こちらは引数が短いため実害は小さい。
- 提案: `breakRawMath` はチャンク列を集めて最後に `T.concat` する形に揃える（`breakLatexComment` と同方式）。`takeBalancedArg` 等も同じ形に統一すると一貫する。

## 5. 用語アンカーの slug が衝突しうるのに検出がない

- 場所: `tools__book-filter__Main.hs:2928` / `termAnchorSlug key = T.map anchorChar (termAnchorKey key)`、`anchorChar c | isAsciiLower c || isAsciiUpper c || isDigit c = c | otherwise = '-'`
- 問題点: 英数字以外をすべて `-` に写すため、空白・ハイフン・記号の違いだけが異なるキー（例: `foo bar` と `foo-bar`）や、大文字小文字だけが異なるキー（`termAnchorKey` が `T.toLower` する）が同じ slug になり、`term-index-…` / `term-def-…` の hypertarget が重複してリンクが取り違えられる可能性がある。節 ID については `duplicateHeaderIds`（4118行）で重複をビルドエラーにする仕組みがあるが、用語アンカーには相当する検査がない。現在の原稿のキー集合で実際に衝突があるかは未確認（要確認）。
- 提案: 文書末の検査に slug 衝突検出を加え、衝突したらキー名を挙げてエラーにする（`duplicateHeaderIds` と同方式）。

## 6. `Emph` だけ `allowLinks` を `False` に落とす非対称性

- 場所: `tools__book-filter__Main.hs:3397` / `processInlineWithLinks allowLinks env (Emph ils) = Emph <$> processInlineSeqWithComments False env ils`
- 問題点: `Strong`、`Underline`、`Strikeout`、`Quoted` 等の兄弟ケースはすべて `allowLinks` をそのまま渡すのに、`Emph` だけが `False` に固定している。結果として、強調の中の数式だけ記法リンクが付かず、「referenced by」索引エントリも生成されない。コメントによる意図の説明もない。意図的なら理由のコメントが、でなければ `allowLinks` の渡し忘れの疑いがある（要確認）。
- 提案: 意図的でないなら他のラッパーと同様に `allowLinks` を渡す。意図的なら、その理由を1行コメントで残す。

## 7. 依存グラフのレイアウトキャッシュが相対パスで、実行ディレクトリと書籍に依存する

- 場所: `tools__book-filter__Main.hs:4155` / `dependencyLayoutCachePath = "build/dependency-graph-layout.cache"`
- 問題点: パスがカレントディレクトリ相対のため、フィルタの起動方法でキャッシュの置き場所が変わる。また英語版・日本語版の両方がリポジトリルートから起動されると同じファイルを共有し、署名（signature）が異なるため正しさは保たれるものの、両書が交互にキャッシュを無効化して再計算が増える可能性がある（要確認: 実際の起動時 CWD は Makefile 側の決め方に依存）。
- 提案: キャッシュパスをメタデータか環境変数で書籍ごとに指定できるようにする。

## 8. `processBlock` の分岐にない入れ子ブロック（Table セル等）はブロック処理を通らない

- 場所: `tools__book-filter__Main.hs:2512`（`processBlock` の case）、末尾の `_ -> walkM (processInline env) b`（2546行）
- 問題点: `BlockQuote`、リスト、`Div`、`Figure` 等は `processNestedBlockList` で再帰するが、それ以外の複合ブロック（代表例は `Table` のセル内ブロック、キャプション）は `walkM (processInline env)` に落ちるため、セル内にある Raw ブロック（mathmeta、記法・用語マーカーのブロック形）は `processBlock` の処理を受けず、`\with` の保留セマンティクスも効かない。インライン側は処理されるため、表のセルにブロック形マーカーを置く原稿が出るまでは無症状のはず（要確認）。
- 提案: `Table` のセルとキャプションを `processNestedBlockList` / `processCaption` で処理する分岐を足すか、「表内ではブロック形マーカーを使わない」制約をコメントに明記する。

## 9. `blockIsStatement` の照合が接頭辞一致で緩い

- 場所: `tools__book-filter__Main.hs:2449` / `any (`T.isInfixOf` txt) [ "\\begin{" <> T.dropEnd 1 envName | (envName, _) <- statementEnvironments]`
- 問題点: 環境名末尾の `*` を落として `\begin{theorem` の接頭辞で照合するため、番号付き環境 `\begin{theorem}` や、将来追加されうる `\begin{theoremFoo}` のような名前でも statement 扱いになる。現行の原稿は starred 環境のみのはずで実害はないが、判定の意図（unnumbered 環境の一覧）より緩い。
- 提案: `\begin{theorem*}` の完全形で照合する（番号なし形も対象にしたいなら、その旨をコメントに明記して両形を列挙する）。

## 10. 日本語索引ローカライズが、最初の失敗で残り全部を打ち切る

- 場所: `tools__book-filter__Main.hs:1046`（`localizeJapaneseIndex` 内の `rewrite` / `nextIndex`）/ `(payload, rest) <- takeBalancedArg body` が失敗すると `nextIndex` 全体が `Nothing` になり、`rewrite` は元のテキストをそのまま返す
- 問題点: 1件の `\index{...}` の括弧が釣り合っていない（または想定外の形）と、そのブロック内の後続の `\index` がすべて未変換のまま残り、エラーにもならない。索引の表示だけの問題とはいえ、黙って部分的に効く形は原因に気づきにくい。
- 提案: 失敗した箇所はそのまま残して走査を続ける（他のマーカー走査が採っている「壊れた箇所を飛ばして続行」方式に揃える）。

## 11. lint の見出し ID 収集がフェンス内コードも走査する

- 場所: `tools__book-filter__Main.hs:209`（`collectMarkdownHeaderIds`）、`213`（`markdownHeaderId`）
- 問題点: 行頭 `#` で始まる行をすべて見出しとして走査するため、フェンスコードブロック内の `# コメント {#sec:...}` のような行でも ID が登録され、本来 dangling な `§{...}` 参照が lint を通過しうる（フィルタ側の `collectHeaderMap` は実見出しだけを見るので、ビルドでは検出される。lint と本体で判定がずれる、という問題）。
- 提案: `lintLineLength` 側にある `isFenceLine` のようなフェンス状態の追跡を ID 収集にも入れる。

## 12. `processDoc` の全書走査の回数が多い

- 場所: `tools__book-filter__Main.hs:919`（`processDoc`）、特に 968–985行の連続する `walk` / `walkM`
- 問題点: 依存グラフ置換（ブロック・インライン各1回）、節参照解決（3回）、HTML コメント除去（2回）、生引用の展開（2回）、ブックマーク描画、索引ローカライズ（2回）と、全書に対する走査が10回前後積み重なっている。各走査は線形でも、260万字規模の文書では定数倍の合計が無視できない。要確認（実測の内訳は未確認で、支配的なのは Pandoc の JSON 入出力や依存グラフ計算の可能性もある）。
- 提案: 計測で無視できなければ、独立な置換同士（コメント除去と節参照など）を1回の走査に融合する。現状維持でも、走査回数が意図的なトレードオフである旨を `processDoc` のコメントに残しておくと判断材料になる。

## 確認して問題なかった主な点

- `SectionRef.nextSectionRef` の境界（閉じ括弧なし、空 ID）はドキュメントどおりの挙動だった。
- `statementEnvironments`（Haskell 側12件）と `tools/booklink_sourcemap.py` の `STATEMENT_ENVS`（12件）は一致していた。
- `isUsedIn` のバックスラッシュ偶奇による左境界判定は、`\\name` 等のケースでも TeX の解釈と一致していた。
- golden テストは記法・用語・mathmeta・見出しブックマーク・日本語索引・節参照と、エラー系 fixture をカバーしている。今回の指摘のうち 1・3 は、そのカバーの外側（lint/inject-booklinks サブコマンドと生引用のプロセス起動）に関するもの。

## 以上、指摘終わり

---

# 付録: バッチ F2

# コードレビュー バッチF2（sunaemon/math-private @ 9d6e65df）

対象: tools/book-filter/DependencyGraph.hs、tools/book-filter/SectionRef.hs、tests/run-book-filter-golden.hs、math-project.cabal、cabal.project。本文（原稿）は対象外。著者がコメントで意図を明記した設計（レイアウトのメモ化方式、unsafePerformIO の計時計装、isTexFormat の意図的な複製、SectionRef の未閉鎖時の契約など）は指摘にしていない。

指摘は計9件（DependencyGraph.hs 5件、テスト 4件）。SectionRef.hs と cabal 定義にはコード上の指摘なし（確認範囲は各節に記載）。

## DependencyGraph.hs

### 1. レイアウトキャッシュの署名が、レイアウトを決める定数の大半をカバーしていない

- DependencyGraph.hs:1218-1231 / `"refinement-candidates=8", "node-clearance=1.45", "edge-direction-weight=1.25", "edge-direction-attraction=0.08", "edge-length-weight=0.04"`（署名への定数の列挙はこの5件のみ）
- 問題点: 署名に含まれる数値定数は上記5件だけで、しかも実定数（`nodeClearance = 1.45` は1009行の where 束縛、`refinementSwapCandidateCount = 8` は1022行）からの導出ではなく手写しのリテラルである。一方、`annealingSteps = 3000`（559行）、`initialTemperature = 2.45`・`springLength = 1.85`（1017-1018行）、`nodeRepulsion = 0.38`（1007行）、`edgeClearance = 0.92`、`partAttraction = 0.02`、Newton 法側の `polishIterations`/`polishEpsilon`/`polishMaxStep`、緩和スワップの間隔など、最終配置を変える定数は署名に入っていない。これらを変更しても（あるいは実定数だけを変更して署名リテラルを直し忘れても）署名が一致し続け、旧パラメータで計算されたキャッシュ位置が「ヒット」として再利用される。ヒット経路で再実行されるのは衝突分離だけなので、パラメータ変更が描画に反映されないことに気づく手段がない。
- 提案: 署名リテラルを実定数から組み立てる形にし、レイアウトに効く定数を網羅する。難しい場合は、定数を1か所のレコードに集約して署名にその `show` を含めるか、定数を触ったら `dependency-layout-v1` の版を上げる運用をコメントに明記する。

### 2. 辺が上位18件に無言で切り取られ、切り捨てられた章がグラフから消える

- DependencyGraph.hs:154 / `take 18 . sortOn (\edge -> (negate (edgeCount edge), ...))`
- 問題点: `edgeCounts` の全辺ではなく参照数上位18件だけが `dgEdges` になり、ノード・部グループ・レイアウト・相互辺もすべてこの18件から導出される。弱い参照しか持たない章は、辺が欠けるだけでなくノードごとグラフから消える。18 という数にはコメントがなく、`DependencyGraphPlan` のコメントが "the edges (full set and the parted subset...)" と読める点とも齟齬がある（実際は full set ではない）。生成される TikZ のヘッダにも切り捨ての記録は残らない。要確認: 上位18件への制限自体は意図的な可能性が高いが、少なくとも現状では読み手が「全章の依存関係」だと思って図を解釈する余地がある。
- 提案: 意図的なら定数に名前と理由のコメントを付ける（例: `maxDrawnEdges`）。あわせて、切り捨てた辺数・ノード数を生成コメントに出すと、図の解釈違いを防げる。

### 3. 部の検出が RawBlock 内の `\part{` 部分文字列に依存している

- DependencyGraph.hs:275 / `"\\part{" `T.isInfixOf` txt`
- 問題点: tex 形式の RawBlock のどこかに `\part{` が現れれば部として数えるため、コメントアウトした `\part{...}`、コード掲載やマクロ定義中の文字列でも幽霊の部が立つ。逆に1つの RawBlock に `\part` が2つあっても1つとしてしか数えられず、以降の部番号（ローマ数字）と部所属がずれる。要確認: 実際の原稿では部指令が単独の RawBlock で現れる運用だと思われるが、検出条件が文書化されておらず、将来の原稿変更で静かに壊れる。
- 提案: 行頭（空白除去後）で `\part{` に一致する行だけを数える、程度の絞り込みでも誤検出は大きく減る。あるいは現行ヒューリスティクスの前提をコメントに明記する。

### 4. 部の枠の行高さが2行分までしか用意されていない

- DependencyGraph.hs:496 / `| row <- [0, 1] ]`（`rowHeights` の定義。列側は `groupCol = groupIdx `mod` 2` で常に2列なので問題ない）
- 問題点: `groupRow = groupIdx `div` 2` は上限がないのに、`rowHeights` は行0・1しか計算しない。部が7つ以上（行3以降）になると、`offsetFor` の `take idx` が要素不足のまま合計するため、その行の枠が手前の行と重なる。現在の5部（3行）では行2のオフセットが偶然正しくなるため表面化しない。`romanNumeral` のコメントが「部数が控えめである前提」を断っているのは承知のうえで、壊れ方がエラーではなく静かな重なりである点だけ要確認として挙げる。
- 提案: `rowHeights` を実際の行範囲 `[0 .. maxRow]` から作る。あるいは前提を超えたら落とすよう、グループ数に上限チェックを入れる。

### 5. キャッシュ座標のパースが NaN / Infinity を受理する

- DependencyGraph.hs:1315-1319 / `case reads input of [(value, "")] -> Just value`
- 問題点: `reads` は `"NaN"` や `"Infinity"` も Double として受理する。署名行さえ一致すれば、壊れた（または手編集された）キャッシュの NaN 座標がそのまま通る。NaN との比較はすべて False になるため `separateDependencyNodes` の衝突検出も働かず、TikZ に `NaN` が出力されて LuaLaTeX 側で原因の分かりにくいエラーになる。
- 提案: `readMaybeDouble` で `isNaN` / `isInfinite` を弾く。有限でない値が1つでもあればキャッシュ全体をミス扱いにするのが安全。

## SectionRef.hs

指摘なし。確認範囲: `nextSectionRef` の境界条件を文書コメントの契約と照合した。未閉鎖の `§{`（後続に `}` なし）は Nothing、`§{}` は空 id で Just、`§{a§{b}` は最初の `}` までを id とする、`§` 単独や空文字列は Nothing、で、いずれも実装とコメントが一致している。 id 内に `}` を含められないこと、未閉鎖を「参照なし」として扱うこともコメントで明示された意図的な契約なので指摘にしない。なお、この境界入力群（未閉鎖・空 id・連続参照）自体を固定するテストが見当たらない点は、下記6の守備範囲の問題に含めた。

## tests/run-book-filter-golden.hs と cabal 定義

### 6. 依存グラフの「収集セマンティクス」を検証するテストがない

- tests/run-book-filter-golden.hs:177-186 / `"dependency graph tolerates a chapter outside any \\part"`（成功ケースはこの1件のみで、終了コードしか見ていない）。レイアウト衝突テスト（266行〜）は配置の不変条件をよく検証しているが、対象は座標の妥当性だけである
- 問題点: 辺の向き（参照元→参照先のどちらを `edgeFrom` とするか）、参照数の集計、章への帰属、部のグループ化、相互辺の判定といった `planDependencyGraph` の意味論は、どのテストでも出力内容を検証されていない。レイアウト結果が移植性のため golden 化できない事情はコメントのとおりだが、plan 段階の辺集合・カウント・グループは決定的であり検証可能なのに、回帰（例: 辺の向きの取り違え、帰属章のずれ、18件切り捨ての境界）を作っても現行スイートは緑のままになる。あわせて、SectionRef の境界入力（未閉鎖の `§{`、空 id、連続参照）を固定するフィクスチャも見当たらない（未閉鎖を Main 側の lint が検出しているかは本バッチの対象外のため要確認）。
- 提案: `planDependencyGraph` を小さい Pandoc 値で直接叩くユニットテストを足すか、辺一覧を決定的なテキストで出すデバッグ経路を用意して golden 化する。SectionRef については `nextSectionRef` の境界ケースだけでも表形式のテストがあると、トークナイザ共有化の目的（スキャナ間のずれ防止）を固定できる。

### 7. 一時ディレクトリ名が固定で、並行実行が互いを壊す

- tests/run-book-filter-golden.hs:47-48 / `let tmp = tmpBase </> "book-filter-golden"` の直後に `removeIfExists tmp`
- 問題点: 共有の一時領域に固定名のディレクトリを作り、開始時に再帰削除する。同じマシンで2つのチェックアウトや CI ジョブが同時に走ると、一方が他方の作業中ディレクトリ（golden の actual 出力、layout-collision のキャッシュ）を消したり読み違えたりして、無関係な失敗や、逆に失敗の見落としが起こりうる。
- 提案: プロセスIDやランダムなサフィックスで一意なディレクトリ名にする（例: `book-filter-golden-<pid>`）。終了時の掃除もあわせて行うと共有領域に残骸が残らない。

### 8. 外部バイナリ（pandoc / diff）の不在が「失敗」ではなく例外になる

- tests/run-book-filter-golden.hs:40-42 / 事前確認は `filterBin` の存在だけで、`runPandoc`（555行〜）と `diffFiles`（570行〜）が呼ぶ `pandoc` と `diff` は未確認
- 問題点: `readProcessWithExitCode` は実行ファイルが存在しない場合に ExitFailure を返すのではなく例外を投げる。pandoc や diff がない環境では、スイートは失敗リストを出す前に異常終了し、「どのテストがなぜ落ちたか」が分からない。golden の期待ファイルが欠けた場合の `readFile` 例外も同様に全体を落とす。
- 提案: main の冒頭で pandoc / diff の存在も確認して分かりやすく落とすか、各 `run*` を例外捕捉して失敗リストの1項目に変換する。

### 9. 失敗ケースの照合文字列が弱く、別の失敗を拾う余地がある

- tests/run-book-filter-golden.hs:122 / `"notation used before"`（118行の `"[notation-filter] notation used before \\define or \\forward:"` と比べて接頭辞も対象記法の限定もない）
- 問題点: "later embedded metadata does not authorize earlier notation" ケースの期待文字列は、記法フィルタの複数の異なる失敗メッセージに部分一致しうる汎用的な断片である。このケースが想定と違う理由で落ちるようになっても（例: 順序判定ではなく別の検証で落ちても）、メッセージにこの断片が含まれれば合格してしまう。逆に、文言の表層変更だけで無関係に壊れる側面もある。要確認: 部分一致方式自体は他のケースでも使われており運用上の割り切りだと思われるが、この1件は同種のケースより一段弱い。
- 提案: このケースも118行側と同程度に、フィルタ名と状況を含む文字列へ寄せる。

### cabal 定義（math-project.cabal / cabal.project）

指摘なし。確認範囲: 実行ファイル側は `-Wall` と抑制理由のコメントが整合していること、test-suite の依存が実行に使う範囲（base / directory / filepath / process）をカバーしていること、`cabal.project` で index-state とコンパイラが固定され再現性が担保されていること。テストが外部バイナリに依存する点は cabal では宣言できないため、上記8に含めた。

## 以上、指摘終わり

---

# 付録: バッチ P1

# バッチP1: booklink 系 Python ツール群レビュー

対象: sunaemon/math-private @ 9d6e65df の `tools/booklink_sourcemap.py`、`tools/booklink_coverage.py`、`tools/booklink_audit.py`、`tools/project_translation_sourcemap.py`。呼び出し側の前提として `Makefile` と `tools/books_mk.py` も参照した。本文（原稿）は対象外。

全体としては、シンボリックリンクを解決しない語彙的パス扱い、skip と booklink の矛盾検出、射影できない場合に推測せずエラーにする方針など、設計判断がコメントで明示された丁寧な実装である。以下はその上での指摘。

## tools/booklink_sourcemap.py

### P1-1（性能・中〜高）span_json が全文の行オフセット表を呼び出しごとに再構築する

- 箇所: `tools/booklink_sourcemap.py:415` `def span_json(text, start_offset, end_offset)` 本体で `offsets = line_offsets(text)` を毎回実行。呼び出し側は `:563`（tex_marker_match_for_entry）、`:388`、`:592`、`:619`、`:663`、`:680`。
- 問題点: 特に `:563` は `attach_tex_matches` からエントリごとに呼ばれ、そのたびに生成 .tex 全文（数MB）の `line_offsets` を再計算する。本書規模（約1,900エントリ）では、オフセット表構築だけでエントリ数×全文走査になり、sourcemap 生成時間の支配項になりうる。skip span（`:388`）や章単位の match（`:619` 等）でも章全文について同じことが起きる。
- 提案: `span_json` が事前計算した `offsets` を受け取る形に変え、tex 全文・章ごとの offsets は呼び出し側で一度だけ作って使い回す。`offset_to_line_column(offsets, ...)` は既に offsets を引数に取るので、インターフェースは揃えやすい。

### P1-2（性能・中）章テキストの再読込と statement 解析が Lean ファイル単位・マーカー単位で繰り返される

- 箇所: `tools/booklink_sourcemap.py:827` `build_combined_sourcemap` が Lean ファイルごとに `:764` `build_sourcemap` を呼ぶ。`statements_by_source` キャッシュは1回の `build_sourcemap` 内だけ有効。`match_statement` の excerpt 分岐は候補 statement ごとに `statement.source.read_text(...)`（`:650`、`:656`）を実行し、`find_prose_match`（`:600`）もマーカーごとに章全文を読み直す。`chapter_rank_map`（`:714`）も Lean ファイルごとに manifest を glob し直して読み直す。
- 問題点: 同じ章を形式化する Lean ファイルが複数あると `parse_book_statements` が「章 × ファイル数」回走り、prose マーカーが多い章では全文読込がマーカー数だけ重なる。Makefile の filter sourcemap 対象（`$(BOOKLINK_LEANS)` は全書分）と viewer sourcemap 対象の両方でこのコストを払う。
- 提案: 章テキスト・`parse_book_statements` 結果・`chapter_rank_map` を `build_combined_sourcemap` 単位で共有するキャッシュに上げる。`match_statement` には statement と一緒に読み済みテキストを渡す。

### P1-3（正しさ・要確認・中）find_next_decl が partial / protected 等の宣言を見落とし、後続の宣言にマーカーを誤って結び付ける

- 箇所: `tools/booklink_sourcemap.py:170` `find_next_decl` の `decl_prefix = r"(?:@\[[^\]]+\]\s*)*(?:private\s+)?(?:noncomputable\s+)?"`。
- 問題点: マーカー直後の宣言が `partial def`、`protected theorem`、`unsafe def` 等の場合、正規表現が一致せず走査がその宣言を素通りして、次の宣言をマーカーの所有者として返す。declName / declLine が黙ってずれ、後段の TeX スパン対応付け（`tex_marker_match_for_entry`）まで誤る。対象 Lean ファイル群にこうした宣言への booklink が無ければ実害はない（要確認）。
- 提案: prefix に `protected`、`partial`、`unsafe`、`scoped` 等を追加するか、一致しない宣言行にマーカーが隣接していたらエラーにする。

### P1-4（正しさ・要確認・中）find_decl_end_line が宣言内部の最初の空行で打ち切られる

- 箇所: `tools/booklink_sourcemap.py:158` `find_decl_end_line`。「if not stripped or ...: break」。
- 問題点: 宣言開始後の最初の空行で decl の終端とみなす。証明の内部に空行を含む宣言（tactic ブロックの段落分け等）では `declEndLine` が途中で切れ、viewer の Lean 側ハイライト範囲が短くなる。「宣言内に空行を入れない」運用前提なら問題ないが、その前提はコードにもコメントにも書かれていない。
- 提案: 前提ならコメントに明記する。そうでなければ、次の宣言・マーカーまでの範囲など、空行に依存しない終端判定に変える。

### P1-5（正しさ・低）find_next_decl のスキャナが文字リテラルと Unicode 識別子を扱わない

- 箇所: `tools/booklink_sourcemap.py:170` のコメント/文字列状態機械と、宣言名の文字集合 `[A-Za-z0-9_'.]+`。
- 問題点: `'"'` のような文字リテラルがあると `in_string` が反転し、その行の残りと後続行の宣言検出がずれる可能性がある。また宣言名にギリシャ文字等の Unicode 識別子が含まれると名前が途中で切れる。
- 提案: 文字リテラル `'…'` を文字列と同様に読み飛ばす。名前の文字集合を Lean 識別子の範囲に広げる。

### P1-6（正しさ・低〜中）parse_skip_spans は不整合な skip 注釈を黙って読み飛ばす

- 箇所: `tools/booklink_sourcemap.py:352` `parse_skip_spans`。対応のない `-end` は「if not stack: continue」、閉じられていない `-begin` はスタックに残ったまま捨てられる。
- 問題点: 同じ入力に対し `booklink_coverage.py` の `ScopeResolver` は ValueError を出す。つまり注釈の誤りを検出するのは coverage 経路だけで、sourcemap 単体の生成（Makefile の filter/viewer sourcemap 対象）では、閉じ忘れた skip 領域が「範囲なし」として静かに処理され、陰影付けもされないままになる。
- 提案: `parse_skip_spans` でも未閉じ・余剰のマーカーをエラーにするか、少なくとも警告を出す。検証規則は coverage 側と揃える。

### P1-7（保守性・中）formalization 注釈の文法が3実装に分散し、範囲と理由の解釈が食い違う

- 箇所: `tools/booklink_sourcemap.py` の `SKIP_COMMENT_RE`（`:311` 付近）と `skip_reason`（`:317`）、`tools/booklink_coverage.py` の `_SCOPE_ANNOTATION` と `_clean_reason`（`:226`）、`tools/books_mk.py` の `FORMALIZATION_SKIP_PATTERN`。
- 問題点: 同じ注釈言語を3つの正規表現が別々に定義している。さらに解釈も完全には一致しない。(a) 領域の範囲: sourcemap は begin コメントの開始位置から end コメントの終了位置まで、coverage は begin コメントの終了位置から end コメントの開始位置までを領域とする。(b) 理由文字列: sourcemap は外側の括弧を1組だけ剥がし、coverage は `strip("()")` で前後の括弧を何組でも剥がすため、`((理由))` のような注釈で両ツールの出す reason が異なる。文法や解釈を変えるときに片方だけ直す事故が起きやすい（現に coverage 側には、陰影モデルとの不整合を塞ぐための `check_shading_skips_unlinked` という追加の照合が必要になっている）。
- 提案: 注釈の走査と範囲・理由の正規化を `booklink_sourcemap` 側の単一実装に寄せ、coverage と books_mk はそれを使う。少なくとも範囲と理由の定義がどちらか一方にしかない現状は解消したい。

### P1-8（正しさ・要確認・低）parse_tex_booklink_spans が2形式のスパンを同じリストに混ぜる

- 箇所: `tools/booklink_sourcemap.py:429` `parse_tex_booklink_spans`。`% BOOKLINK-START...` コメント形式を集めた後、同じ `spans` に `\BooklinkStart` コマンド形式も追加して返す。
- 問題点: 生成 .tex に両形式が同一スパンについて混在すると、スパンが二重に数えられ、`texMarkerCount` が膨らみ、`tex_marker_match_for_entry` の「n 番目のエントリ ↔ n 番目のスパン」対応がずれる。現行の book-filter が片方の形式しか出さないなら実害はない（要確認）。
- 提案: 両形式が見つかったらエラーにするか、形式ごとに分けて片方を優先する。

### P1-9（正しさ・低）tex_marker_match_for_entry が1スパンを二重に数える場合がある

- 箇所: `tools/booklink_sourcemap.py:553` `decl_spans = [span for span in spans for name in span.names if lean_name_matches(decl_name, name)]`。
- 問題点: 1つのスパンの `names` に同じ宣言へ一致する名前が2つ含まれていると、そのスパンが候補リストに2回現れる。以後のエントリの順序対応付けが1つずつずれ、関係ないスパンに結び付く。
- 提案: スパン単位で重複を取り除いてから候補リストを作る。

### P1-10（保守性・低）strip_latex_macros の置換が前方一致で作用する

- 箇所: `tools/booklink_sourcemap.py:82` `strip_latex_macros` の `replacements` 辞書を `text.replace(old, new)` で順に適用。
- 問題点: `\R` の置換は `\RealSequenceSpace` の先頭にも当たり、現在は置換結果が偶然同じ文字列になるため壊れていないが、マクロ名の追加・変更で静かに化ける余地がある。タイトル比較の正規化専用なので影響は曖昧一致の精度に限られる。
- 提案: マクロ名の境界（後続が英字でないこと）を条件にする。

## tools/booklink_coverage.py

### P1-11（正しさ・中）全マーカーが unresolved の章がレポートから丸ごと消える

- 箇所: `tools/booklink_coverage.py:123` `covered_spans_by_source` が matched / weak なエントリのある章だけをキーにし、`main`（`:551`）はそのキー集合だけを報告する。
- 問題点: 章を指すマーカーがすべて解決に失敗した場合、その章は「0% カバー」としてではなく、レポートに一切現れない。タイトル変更等で対応が全滅した章ほど見えなくなるのがこのツールの目的（ギャップ検出）と逆行する。`booklink_audit.py` は manifest の全章を走査してこの穴を塞いでいるが、coverage 単体では検出できない。
- 提案: エントリが存在する章は、解決済みスパンがゼロでも報告に含める（全単位 uncovered として出す）。

### P1-12（保守性・低）未使用の定数と引数が残っている

- 箇所: `tools/booklink_coverage.py:202` `DEFAULT_EXEMPT_KINDS` は定義のみで参照箇所がない。`ScopeResolver.classify`（`:278`）の `kind` 引数は本体で使われず、`build_unit` の `scope_kind`（`:377`）ごと死んだ受け渡しになっている。
- 問題点: 「環境種別で免除が決まる」設計が残っているように読め、docstring の「環境名では判断しない」という方針と矛盾して見える。
- 提案: 削除する。

### P1-13（正しさ・要確認・低）空行なしで statement 環境を含むブロックが二重に数えられる

- 箇所: `tools/booklink_coverage.py:513` `units_for_source`。prose 単位は `paragraph_blocks` のブロック全体で、ブロックの内容先頭が statement 範囲外なら丸ごと prose 単位になる。
- 問題点: 1つのブロック内に statement 環境とその前後の散文が空行なしで混在すると、環境部分が statement 単位と prose 単位の両方に含まれ、文字数・カバー率が二重計算される。通常の執筆形式（環境の前後に空行）では起きない（要確認）。
- 提案: prose ブロックから statement 範囲を差し引いた残りを単位にするか、混在ブロックを検出して警告する。

### P1-14（性能・低）units_for_source 内で章ファイルの再読込が重なる

- 箇所: `tools/booklink_coverage.py:514` で読み込んだ本文に対し `:518` `bk.parse_book_statements(path)` が再読込し、`check_shading_skips_unlinked`（`:498`）の `bk.parse_skip_spans(path)` がさらに再読込する。その前段の `covered_spans_by_source` も combined map 構築で全章を読んでいる。
- 問題点: 1章につき最低3回の全文読込＋再解析が、既に sourcemap 構築で済んでいる走査と重なる。監査・報告用途なので許容範囲だが、P1-2 と合わせると全章走査の重なりが大きい。
- 提案: 読み込み済みテキストを受け取る版の関数を用意し、`units_for_source` 内で共有する。

## tools/booklink_audit.py

### P1-15（保守性・中）manifest の読み方が検証付きの共通関数を経ず、reviews の有無への対応も非対称

- 箇所: `tools/booklink_audit.py:379` `json.loads(manifest.read_text())["chapters"]`。一方、他ツールは `book_manifest.read_manifest` で型検証して読む。また `:385` の reviews ファイルは存在しないと FileNotFoundError のトレースバックで落ちるが、scope reviews 側（`:388`）は `exists()` で任意扱いにしている。
- 問題点: マニフェスト形式の解釈箇所が増え、検証水準がツールごとに違う。reviews ファイルのないチェックアウト（公開側など）で監査を回すと、整ったエラーではなくトレースバックになる。
- 提案: `read_manifest` を使う。reviews も scope reviews と同様に「なければ空」か、欠けている場合の明示エラーに統一する。

### P1-16（正しさ・低）read_text の encoding 省略が7箇所ある

- 箇所: `tools/booklink_audit.py:74`、`:160`、`:379`、`:385`、`:388`、`:390`、`:400` の `read_text()`。他3ツールは全箇所で `encoding="utf-8"` を明示している。
- 問題点: ロケールのデフォルトエンコーディングが UTF-8 でない環境では、デコードエラー、あるいは `digest` の指紋が変わって全レビュー判定が失効扱いになる恐れがある。指紋は失効判定そのものに使うので、環境依存性が監査結果に直結する。
- 提案: 全箇所に `encoding="utf-8"` を付ける（指紋用途はバイト列のままハッシュするのがより確実）。

### P1-17（性能・低）監査全体で全章走査が何重にも重なる

- 箇所: `tools/booklink_audit.py` の `main` が全 Lean ファイルで `bk.build_combined_sourcemap` を構築した後、章ごとに `scan_source` → `cov.units_for_source` で再解析する。
- 問題点: P1-2・P1-14 と同型の重複で、監査1回あたり章集合を何度も読み直す。たまに回す監査なので実害は小さいが、大規模化すると最初に効く箇所になる。
- 提案: P1-2 のキャッシュ共有が入れば自動的に軽くなる。現状でも、監査が遅くなった場合はまずここを見るべき箇所として挙げておく。

## tools/project_translation_sourcemap.py

### P1-18（正しさ・要確認・低）weak エントリは射影されず英語のまま JA マップに残る

- 箇所: `tools/project_translation_sourcemap.py` の `project_map`。`match.status == "matched"` のエントリだけを書き換え、skips は無条件に書き換える。
- 問題点: `"weak"` エントリは英語章へのパスと英語オフセットを保持したまま、`root` と Lean パスだけ JA 側に書き換わったマップに混ざる。フォールバックとして意図的なのか、単に対象外なのかがコメントからは読み取れない（要確認）。viewer 側で英語章を指すエントリがどう表示されるかにも依存する。
- 提案: 意図的ならその旨をコメントに書く。そうでなければ weak も射影するか、射影できないエントリは落とす/印を付ける。

### P1-19（保守性・低）検査ツールの private 関数を import している

- 箇所: `tools/project_translation_sourcemap.py:28` `from check_translation_structure import _normalize_math`。
- 問題点: 射影ツールが検査ツールの内部実装（アンダースコア付き）に結合している。`check_translation_structure` 側のリファクタで、正規化の定義が変わったり関数が動いたりすると、射影側が静かに影響を受ける。Makefile の依存宣言にもこの結合は現れている（射影ツールの前提に `tools/check_translation_structure.py` が並ぶ）。
- 提案: `_normalize_math` を共通モジュールへ移すか、公開名にして両ツールから使う。

### P1-20（正しさ・要確認・低）PO パーサが fuzzy エントリを区別しない

- 箇所: `tools/project_translation_sourcemap.py` の `read_po`。コメント行は一律に読み飛ばされ、`#, fuzzy` の付いたエントリも通常の翻訳として扱われる。
- 問題点: fuzzy な msgstr が生成済み日本語 Markdown に実際に現れるかは po4a 側の fuzzy 扱いに依存する。不一致の場合は `po_segments` の出現回数検査でエラーになるため黙った誤射影にはならないが、前提が暗黙になっている。
- 提案: fuzzy エントリを未翻訳として扱うか、前提を docstring に明記する。

### P1-21（正しさ・低）章パスの解決が実行時の cwd に依存する

- 箇所: `tools/project_translation_sourcemap.py` の `load_projections`。manifest 記載の章パスをそのまま `Path(...).resolve()` する。
- 問題点: repo ルート以外から実行すると、章パスが別の場所を指して読み込みエラー（あるいは最悪、別ファイルの読み込み）になる。Makefile 経由では常にルートで実行されるため実害はないが、`booklink_sourcemap.py` の `--root` のような基準指定がなく、単体実行時の前提が見えない。
- 提案: manifest ファイルの位置を基準に解決するか、前提を docstring に明記する。

## 以上、指摘終わり

---

# 付録: バッチ P2

# バッチP2: 翻訳チェック・ビルド検証系 Python ツール群

対象: sunaemon/math-private @ 9d6e65df の次11ファイル。
tools/check_translation_structure.py、tools/check_translation_workflow.py、tools/check_translation_terms.py、tools/audit_translation_coverage.py、tools/split_skip_blocks.py、tools/validate_book_build.py、tools/split_preview_tex.py、tools/migrate_lean_modules.py、tools/vendor_notices.py、tools/po_diff.py、tools/prepare_pandoc_templates.py。
あわせて Makefile / lefthook.yml /.github/workflows/check.yml での呼び出し方を確認した（lint-translation は workflow、lint-translation-terms は terms、validate-tex/validate-debug は validate_book_build を使用。audit / split_skip_blocks / migrate は Makefile・CI のいずれからも呼ばれない手動ツール）。
一部の指摘はモジュールを実際に実行して確認した（その旨を明記）。

総評: 例外を整形して終了コードを返す設計が大半で水準は高い。構造チェック（1=差異 / 2=実行失敗）と比べ、他ツールの終了コード規約の不統一と、検出漏れ2件（P2-1、P2-8）が主な論点。

---

## tools/check_translation_structure.py

### P2-1 任意引数つき \cite を検出できない
- 該当（71行）: `_LATEX_CITATION = re.compile(r"\\(?:[A-Za-z]*cite[A-Za-z]*)\s*\{(?P<keys>[^{}\n]+)\}")`
- 問題: コマンド名の直後に `\s*\{` を要求するため、`\cite[Chapter 2]{key}` や `\citep[see][p. 5]{key}` のような任意引数つき引用は丸ごと取りこぼす。実地確認: `"See \\cite[Chapter 2]{knuth84} and \\cite{lamport94}."` から抽出される引用は `lamport94` のみで、`knuth84` が消える。生TeXブロック内の引用がこの形式だと、日英で引用を落としても・増やしても検出されない。
- 提案: コマンド名と `\{` の間に `(?:\[[^\]\n]*\])*` を許す。

### P2-2 Pandoc 引用キーが文末の句読点を吸い込み、日英で非対称になる
- 該当（70行）: `_PANDOC_CITATION = re.compile(r"(?<![\w@])@(?P<key>[A-Za-z0-9][A-Za-z0-9_.:+/?<>~&%#$-]*)")`
- 問題: キーの文字集合に `.` と `:` が含まれるため、文末・節末の裸の `@key` が句読点ごとキーになる。実地確認: `"@lamport94."` は `lamport94.` として抽出される。英語原文は `.` で終わるが日本語訳は `。` で終わる（`。` は文字集合外）ため、正しい翻訳でも citations の多重集合が一致せず誤検出になる。引用は多重集合比較（順序なし）なので、文末の著者名引用が1つでもあれば章全体が落ちる。
- 提案: 抽出後に末尾の `[.:]+` をキーから落とす、または文字集合から末尾句読点を除く形に境界処理を入れる。

### P2-3 インラインコードのマスクが CommonMark のバッククォート列規則に従わない
- 該当（146–166行）: `_inline_code_ranges` は開始列と「同じ文字列」の次出現を閉じ位置とする
- 問題: CommonMark では閉じ列は開始列と正確に同じ長さの列でなければならず、より長い列の一部は閉じにならない。本実装は部分一致で閉じるため、エスケープされていない単独バッククォート等でマスク範囲がずれ、構造トークンの見落とし・誤認がありうる。通常のコードスパンでは問題にならない。
- 提案: 閉じ候補が前後ともバッククォートに接していない（独立した同長列である）ことを確認する。

### P2-4 閉じられていない YAML front matter を本文として扱う
- 該当（110–117行）: `_yaml_range` は閉じ行が見つからなければ `None` を返し、マスク自体を諦める
- 問題: 壊れた入力でも落ちないのは良いが、front matter 内の行（YAMLコメントの `#` 行など）が見出しとして誤認されうる。実地確認: 閉じのない `---` でも後続の見出し抽出は続行される。
- 提案: 開始行があるのに閉じがない場合は StructureParseError にして「パース不能」として報告する方が、誤った比較結果を出すより安全。

## tools/check_translation_workflow.py

### P2-5 構造チェックの StructureParseError が捕捉されず traceback になる
- 該当（233行）: `diagnostics = check_translation_structure.compare_files(chapter.source, rendered)`／（290行）: `except (OSError, UnicodeError, TranslationCheckError)`
- 問題: `compare_files` は未閉じの波括弧引数などで `StructureParseError`（ValueError のサブクラス。実地確認済み）を送出しうるが、main の捕捉対象に含まれていない。壊れた生成MDがあると整形済みメッセージではなく traceback で落ちる（終了コードは偶然1のまま）。同じファイルの `_check_terminology`（157–163行）は StructureParseError を捕捉して包んでおり、対照的。
- 提案: check_workflow 内で compare_files の呼び出しを包むか、main の捕捉に StructureParseError を追加する。

### P2-6 検査対象の章集合が translation-status.json のみで決まる
- 該当（69–122行）: `_load_status` が status の `chapters` だけを走査対象にする
- 問題: po4a 設定（JA_PO4A_CONFIG）側に章があって status に記録がない場合、その章の PO は msgfmt/fuzzy/未訳チェックも構造チェックも受けずに素通りする（po4a は一時出力へ生成するが誰も比較しない）。逆方向（status にあって設定にない）は msgcmp や生成物欠落で落ちるため非対称。Makefile のコメント「New draft chapters enter the build only after their catalogs and source records exist」が示すとおり二つの台帳の手動同期が前提になっており、ずれが無言で通る。
- 提案: po4a 設定の章集合と status の章集合の一致自体をチェック項目に加える。

### P2-7 --write-generated の書き込みが非原子的
- 該当（243–249行）: `chapter.translated.write_bytes(content)`
- 問題: 「後の章で失敗したら何も変えない」という設計（238行コメント）を検証段階では守っているが、最終書き込み自体は一時ファイル経由でないため、書き込み中の割り込みで生成MDが中途半端な状態になりうる（git管理下なので復旧は可能）。
- 提案: 同一ディレクトリの一時ファイルに書いてから rename する。

## tools/check_translation_terms.py

### P2-8 msgstr 中の `%` 以降を行末までコメントとして隠してしまう
- 該当（190–193行）: `for match in re.finditer("%", content):` … `hidden.append((match.start(), len(content) if end < 0 else end))`
- 問題: PO の msgstr は Markdown であり、`%` は通常の文字（Pandoc が LaTeX 出力時にエスケープする）であってコメント開始ではない。実地確認: avoid ルール「証人→証拠」に対し `"50%の証人が述べた。"` は違反が検出されず、`%` のない文や次行の「証人」は正しく検出される。パーセント表記を含む文で、その行の残り全体が用語チェックから外れる。生TeX部分のコメントを隠す意図だとすれば範囲が広すぎる。
- 提案: `%` のマスクを mathmeta 環境や生TeXブロック内に限定するか、少なくとも行末までではなく LaTeX コメントとして扱う根拠をコメントに明記する。

### P2-9 他モジュールの private 関数の長さ保存契約に依存している
- 該当（206行）: `visible = "".join("\0" if a!= b else b for a, b in zip(message.msgstr, visible))`、および冒頭の `from check_translation_structure import _brace_argument, _content_text,...`
- 問題: zip による位置合わせは `_content_text` と `_mask_hidden_term_identities` が文字列長を保存することに依存する暗黙契約で、どちらかが長さを変えると黙って位置がずれ、誤検出・検出漏れになる。private 名の import が複数ツールに広がっており、structure 側の内部変更の影響範囲が見えにくい。
- 提案: 長さ保存を前提とする関数群を公開名にするか、契約を docstring に明記し、zip 前に長さ一致を assert する。

### P2-10 終了コードの規約がツール群で不統一
- 該当: 本ファイル main（違反時も例外時も 1）、比較対象として check_translation_structure は 1=差異 / 2=実行失敗、check_translation_workflow は全て 1、validate_book_build は検証失敗 1 / 引数エラー 2（argparse）
- 問題: Makefile・CI は非ゼロを一律に扱うため実害は小さいが、「チェックが落ちた」のか「チェック自体が壊れた」のかを呼び出し側ログで区別できない場面がある。
- 提案: 2=実行失敗の規約を群全体で揃えるか、各ツールの docstring に終了コードの意味を明記する。

## tools/audit_translation_coverage.py

### P2-11 例外処理が皆無で、パスも cwd 相対のハードコード
- 該当（141–160行）: `root = Path.cwd()`、`sources = root / "polish-space/src/polish-space-book.json"`、`by_source[str(chapter.source)]`
- 問題: main 全体に try がなく、誤った cwd で実行すれば FileNotFoundError の traceback で落ちる。また `by_source[...]` は booklink entry が1件もない章で KeyError になりうる（要確認: build_combined_sourcemap が全章分の entry を出すかは未確認）。レポート生成ツールの落方としては荒く、途中までの結果も残らない。
- 提案: 章単位で例外を捕捉して alignmentIssues 相当の記録に落とすか、最低限のトップレベル捕捉と cwd（repo ルート）の検証を入れる。

### P2-12 「レポート生成」か「ゲート」か位置づけが曖昧
- 該当（190行）: `return int(bool(gaps or issues))`
- 問題: docstring と出力（report.md の「未対応・部分対応は…残す」という記述）は監査レポートの体裁だが、未対応があれば終了コード 1 を返す。Makefile・lefthook・CI のいずれからも呼ばれていない（grep で確認）ため現状は無害だが、後で CI に組み込むと「既知の未対応」を恒常的な失敗として扱うことになる。
- 提案: ゲートにするなら docstring と Makefile 側に明記し、レポート専用なら 0 を返す（または `--strict` で切り替える）。

## tools/validate_book_build.py

### P2-13 本の発見ロジックと stem 正規表現が books_mk.py と二重管理
- 該当（24–33行）: `discover_books` の `root.glob("*/src/*.json")` 走査と `re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", stem)`
- 問題: tools/books_mk.py も同じ manifest 走査と stem パターン（STEM_PATTERN）を持ち、検証対象の解釈が二箇所で定義されている。片方だけ変更すると、Makefile が生成する本と validator が見る本の集合・命名規則がずれうる。read_manifest 自体は共有化されているのと対照的。
- 提案: stem パターンと発見ロジックを book_manifest.py 側の共通関数に寄せる。

## tools/split_preview_tex.py

### P2-14 章の対応付けドリフトが warning のみで終了コード 0
- 該当（147–157行、163–169行）: ラベル不一致と `ci!= len(chapter_paths)` の不一致はいずれも `print(..., file=sys.stderr)` のみ
- 問題: 本ツールは Makefile の preview 生成レシピ（Makefile 647–649行）から呼ばれ、出力した units.json が viewer の章対応に使われる。manifest と.tex の章順がずれてもビルドは成功し、位置で対応付けた誤った章名のユニットがそのまま使われうる。「silently mis-mapped ではなく報告する」というコメント（122–126行）の意図からしても、報告先が stderr のみでゲートになっていない点は弱い。
- 提案: 不一致時は非ゼロで終了する（既存運用への影響が大きければ `--strict` を Makefile 側で有効化する）。

### P2-15 エラー経路が SystemExit と return 1 で混在
- 該当（62–66行）: `split_body` 内の `raise SystemExit(...)` と、main の他の失敗経路（return 1）
- 問題: 動作上の差は小さいが、ライブラリ関数側が SystemExit を投げる形は単体テストや再利用時に扱いにくい。
- 提案: split_body は例外（ValueError 等）を投げ、main で捕捉して 1 を返す形に統一する。

## tools/vendor_notices.py

### P2-16 fetch-license の失敗が終了コードに反映されない
- 該当（131–157行）: `fetch_one` は失敗時に `False` を返すが、`cmd_fetch_license` は戻り値を捨てて常に 0 を返す。また（143行）`response.read().decode("utf-8")` の UnicodeDecodeError は捕捉対象（URLError, TimeoutError）外で、`--all` の途中で traceback になりうる
- 問題: ライセンス取得をスクリプトから呼んでも失敗を検出できず、途中まで書けた状態で落ちることもある。
- 提案: 失敗した component があれば非ゼロを返し、decode 例外も捕捉して「leaving unchanged」扱いに含める。

## tools/split_skip_blocks.py

### P2-17 手作業が必要なブロックが残っても終了コード 0
- 該当（130–135行）: `plan_block` が `"MANUAL: no safe automatic cut …"` を返し、main（210行）は常時 `return 0`
- 問題: 手動実行ツールなので致命的ではないが、MANUAL の残件があるかどうかを呼び出し側（や実行したエージェント）が終了コードで判定できず、標準出力の読み落としで見逃しうる。
- 提案: MANUAL が1件でもあれば終了コードを 1 にするか、末尾に残件数のサマリを必ず出す。

## tools/prepare_pandoc_templates.py

### P2-18 caption ブロックの「消滅」ケースが docstring の意図に反して素通りする
- 該当（8–9行、33–42行）: docstring は「Reject a changed upstream table-caption block」とするが、判定は `if "\\captionsetup[table]" in common:` の内側でのみ行われる
- 問題: 上流の common.latex から `\captionsetup[table]` 行自体が消えた（書式変更含む）場合、検査を素通りし、`\usepackage{caption}` だけが無条件に読み込まれる partial が生成されうる。日本語クラスが自前のキャプション組版を持つため避けたいのはまさにその読み込みであり、検出の穴が意図とずれている。最終的には TeX ビルドで失敗するので被害は限定的。
- 提案: `\\usepackage{caption}` が含まれるのに想定ブロックがない場合も ValueError にする。

## tools/migrate_lean_modules.py

### P2-19 一回限りの移行スクリプトの残留と、他ツールとの細部の不統一
- 該当（121行、159行）: `path.read_text()` / `path.write_text(updated)` は encoding 未指定（他ツールは一貫して `encoding="utf-8"` を明示）。また `--diagnostics` の行番号適用（137・146・150行）は `lines[number - 1]` で、ログとファイルがずれていれば IndexError で落ちる（docstring は stale log を使うなと警告済みだが、防御はない）
- 問題: 移行完了後も tools/ に残ることで「現役ツール」との区別がつかず、保守対象が増える。encoding は実行環境のロケール依存になる。
- 提案: 役目を終えているなら削除または `tools/archive/` 等への移動を検討し、残すなら encoding を明示する。

## tools/po_diff.py

### P2-20 引数検証がない
- 該当（16行）: `Path(sys.argv[1])` を無検証で使う
- 問題: 引数なしで実行すると IndexError の traceback になる。git textconv 経由では実害はほぼないが、単体で叩いた際の落方が他のツールと比べて荒い。
- 提案: argv の長さを確認して usage を出す程度で十分。

---

## 集計

- tools/check_translation_structure.py: 4件（P2-1〜P2-4。うち実地検証済みの検出漏れ1件・誤検出1件）
- tools/check_translation_workflow.py: 3件（P2-5〜P2-7）
- tools/check_translation_terms.py: 3件（P2-8〜P2-10。うち検出漏れ1件は実地検証済み）
- tools/audit_translation_coverage.py: 2件（P2-11〜P2-12）
- tools/validate_book_build.py: 1件（P2-13）
- tools/split_preview_tex.py: 2件（P2-14〜P2-15）
- tools/vendor_notices.py: 1件（P2-16）
- tools/split_skip_blocks.py: 1件（P2-17）
- tools/prepare_pandoc_templates.py: 1件（P2-18）
- tools/migrate_lean_modules.py: 1件（P2-19）
- tools/po_diff.py: 1件（P2-20）

合計 20 件（中 7件、低 13件。重大な欠陥はなし）。

## 以上、指摘終わり

---

# 付録: バッチ V1

# バッチ V1: formalization viewer クライアント側レビュー

対象: sunaemon/math-private @ 9d6e65df、`tools/formalization-viewer/src/*.ts`（テスト含む）、`tools/formalization-viewer/styles.css`、`tools/formalization-viewer/index.html`

総評: 全体として設計・コメントの質は高い。innerHTML への挿入は escapeHtml / safeHref でほぼ一貫して守られ、純粋ロジック（permalink、session-store、layout-tree、skip-bands、source-offsets/segments、dropdown-filter、stream-frames、copy-tex）は `node --test` の単体テスト（計123件）に切り出されている。指摘は以下の17件で、重大な XSS や状態破壊は見つからなかった。

## セキュリティ

### V1-1. PDF リンク注釈の URL が safeHref を通らず href に入る
- tools/formalization-viewer/src/pdf.ts:322 / tools/formalization-viewer/src/parallel-pdf.ts:297
- 該当箇所: `box.href = annotation.url;`
- 問題点: util.ts には href 用の検証関数 safeHref（http/https/mailto と相対 URL のみ許可、制御文字除去）があり、manifest 由来の URL（project.repository、ライセンスの source）には app.ts:108,124 で適用されている。しかし PDF の Link 注釈 URL は PDF ファイル由来の外部入力であるにもかかわらず無検証でアンカーの href に設定され、`target="_blank"` でクリック可能になる。`javascript:` 等のスキームが注釈に含まれていればクリック時にページ文脈で実行されうる。現状の PDF は自著の TeX ビルド産物なので現実のリスクは低いが、検証の適用範囲として一貫しない。
- 提案: 両箇所とも `const href = safeHref(annotation.url); if (href) { box.href = href; ... }` とし、空なら内部リンク扱いにもリンク化にもしない。

## 正しさ・堅牢性

### V1-2. parallel-pdf は差し替えられた loadingTask を破棄しない（pdf.ts とのドリフト）
- tools/formalization-viewer/src/parallel-pdf.ts:615
- 該当箇所: `const pdfDocument = await loadingTask.promise; if (token !== parallel.token) return;`
- 問題点: 主 PDF 側は非同期完了後にトークンが古ければ `loadingTask.destroy()` で pdf.js 側ドキュメントを破棄する（pdf.ts:807,822）。peer 側は return するだけで破棄せず、また前回の `parallel.loadingTask` も再初期化時に破棄されない。ピア文書の再読み込み（プレビュー切替や watch 再読込）が重なると、破棄されない pdf.js ドキュメント／ワーカーが残りうる。
- 提案: pdf.ts と同じ規律に揃え、token 不一致時と新規 init 開始時に旧 loadingTask を destroy する。

### V1-3. app.ts の localStorage 直接アクセスが無防備
- tools/formalization-viewer/src/app.ts:206 / :349 / :370 / :1613 / :1620
- 該当箇所: `localStorage.setItem(LAYOUT_STORAGE_KEY, ...)` ほか
- 問題点: session-store.ts は「localStorage は無効化されていると null を返すのではなく throw する」という前提で全アクセスを try/catch している。一方 app.ts 側の保存系（saveLayout、saveMarkHighlights、saveLinkHighlights、sync／行番号トグルの setItem）は無防備で、プライベートウィンドウやストレージが阻害される環境では例外がイベントハンドラを中断しうる。読み側も loadLineNumbers（app.ts 内）等は無防備。
- 提案: 安全な get/set ヘルパを util か session-store 側に置き、app.ts の直接アクセスを全てそれ経由にする。

### V1-4. els.status / mdMeta / leanMeta に対応する要素が index.html にない
- tools/formalization-viewer/src/state.ts:201 / :243 / :244、tools/formalization-viewer/index.html（該当 id なし）
- 該当箇所: `status: document.getElementById("status")`、`mdMeta: document.getElementById("md-meta")`、`leanMeta: ...`
- 問題点: index.html には `status`、`md-meta`、`lean-meta` の id を持つ要素が存在しない（tex-meta のみ存在）。そのため updatePdfStatus は冒頭の `if (!els.status) return;` で常に無言で戻り、宣言名・MD/TeX 行・PDF ページのステータス表示は死んでいる。md/lean ペインの現在ファイル名表示（renderSelectedSources 内の `if (els.mdMeta)`）も同様に常時スキップされる。要確認：意図的に表示をやめた残骸か、HTML 側の脱落か。
- 提案: 表示するなら index.html に要素を追加する。不要なら els の3項目と updatePdfStatus の配線を削除して死んだコードを残さない。

### V1-5. loadLayout が pdf-peer の表示状態を毎回リセットする（要確認）
- tools/formalization-viewer/src/app.ts:196
- 該当箇所: `tree = replaceLeaf(tree, "pdf", { dir: "row", children: [{ pane: "pdf" }, { pane: "pdf-peer" }], ... })`
- 問題点: loadLayout は保存済みツリーから一旦 pdf-peer を removeLeaf で除去し、parallelPdf がある場合は pdf との row 分割として無条件に再挿入する。さらに init は peer のペインチェックボックスを checked=true に固定する。つまり他のペインと違って pdf-peer の非表示は保存されず、リロードのたびに表示へ戻る。製品判断として意図的なら問題ないが、レイアウト永続化の原則からは例外になっている。
- 提案: 意図的であればその旨をコメントに明記する。そうでなければ、保存ツリーに pdf-peer が含まれていた場合のみ再挿入する形にする。

### V1-6. infoview の位置ラベルで列番号だけ 0-based
- tools/formalization-viewer/src/infoview.ts:74
- 該当箇所: `` `${displayPath(...)}:${position.line + 1}:${position.character}` ``
- 問題点: 行は 1-based に補正されているのに列（character）は LSP の 0-based のまま表示される。同ファイルの Messages 側は `character + 1` と補正しており（infoview.ts の renderMessagesSection）、表記が揃っていない。エディタの行:列表記ともずれる。
- 提案: `position.character + 1` に統一する。

### V1-7. renderPdfPage の失敗ページがスクロールのたびに再試行される（軽微）
- tools/formalization-viewer/src/pdf.ts（renderPdfPage の catch 節）
- 問題点: 描画に失敗したページは `rendered=false` のまま残り、renderVisiblePdfPages がスクロールのたびに再試行する。恒常的に失敗するページ（破損・巨大すぎる等）があると再描画と console.error が繰り返される。
- 提案: 失敗回数を pageState に記録し、上限で再試行を止めるか、バックオフを入れる。

### V1-8. event-stream のハンドラ例外が後続ハンドラを止める（軽微）
- tools/formalization-viewer/src/event-stream.ts（attachChannel のリスナ）
- 該当箇所: `for (const handler of this.handlers.get(channel) || []) handler(event.data);`
- 問題点: 1つのハンドラが throw すると同じチャネルの後続ハンドラがそのフレームを受け取れない。現行の登録ハンドラ（lean-lsp は内部で try/catch、file-watch / build-status は安全なパースのみ）は実質安全だが、共有基盤としての防御がない。
- 提案: ハンドラ呼び出しを個別に try/catch し、console.warn に留める。

## 性能

### V1-9. マーカーパレットが全件を毎回 KaTeX 描画し直す
- tools/formalization-viewer/src/app.ts:1004（renderMarkerList）、:933（renderMath）
- 問題点: パレットのリストはフィルタ結果の全マーカー（本書規模では数百件）を毎回のキー入力・ホバー移動で innerHTML ごと再構築し、各行のタイトルを renderMath 経由で KaTeX renderToString し直す。markerInfo 自体はキャッシュされているが、KaTeX の出力文字列はキャッシュされていない。マーカー数が増えるとパレットの入力応答が目に見えて重くなりうる。
- 提案: markerInfo に描画済み HTML（または renderMath の結果）を一緒にキャッシュする。それでも重い場合はリストの仮想化（可視範囲のみ描画）を検討する。

## 保守性

### V1-10. pdf.ts と parallel-pdf.ts の重複が大きく、既にドリフトが始まっている
- tools/formalization-viewer/src/pdf.ts:196 / parallel-pdf.ts:112（computeDocCrop / computeCrop）
- tools/formalization-viewer/src/pdf.ts:294 / parallel-pdf.ts:270（resolvePageLinks / resolvePeerPageLinks）
- tools/formalization-viewer/src/pdf.ts:500 / parallel-pdf.ts:380（computePageLines）
- ほか、スクロールアンカーの capture/restore、バンド描画（renderEntryBands / renderParallelEntryBands）もほぼ同型。
- 問題点: peer 側は「主 PDF の対向物」として意図的に並行実装されているが、クロップ推定・リンク注釈のオーバーレイ化・テキスト行抽出といった実質ロジックが丸ごと複写されている。V1-2（loadingTask 破棄の有無）のような片側だけの修正漏れが既に発生しており、今後も片方だけ直る事故が起きやすい。
- 提案: 状態に依存しない部分（クロップ推定、注釈→オーバーレイ変換、行抽出）を、文書オブジェクトとコールバックを引数に取る共通モジュールへ切り出す。

### V1-11. 中核の状態機械に単体テストがない
- tools/formalization-viewer/src/sync.ts、tools/formalization-viewer/src/lean-lsp.ts、tools/formalization-viewer/src/reload-guard.ts、tools/formalization-viewer/src/build-status.ts / file-watch.ts
- 問題点: テストは純粋モジュールに集中し（skip-bands 40件、layout-tree 21件、event-stream 14件など計123件）、方針として一貫している。ただし sync.ts のスクロール抑制ウィンドウ（300ms／リンク跳躍時 1200ms）や lean-lsp.ts の heal 単一飛行・backoff といった不変条件は、コメントで丁寧に説明されている一方で回帰テストがない。event-stream が注入可能な設計になっている以上、フェイククロックとフェイク転送でこれらもテスト可能なはずで、守備範囲の線引きが惜しい。要確認（e2e 側でカバーしている可能性は未確認）。
- 提案: sync の navigateTo／抑制解放と lean-lsp の scheduleHeal について、タイマと fetch を注入可能にして最小の回帰テストを足す。

### V1-12. app.ts が依然として巨大（2,715行）
- tools/formalization-viewer/src/app.ts 全体
- 問題点: モジュール分割は進んでいるが、app.ts にはレイアウトツリーの DOM 構築、スプリッタのドラッグ、ペインのドラッグ＆ドロップ、マーカーパレット、LSP のゴール／ホバー連携、ファイル監視の振り分けがなお同居する。個別の関数はコメントで区切られているため読解は可能だが、変更の影響範囲が広く、上の V1-9 のような性能問題もこのファイルに集中する。
- 提案: 次の分割候補として wireEvents 群（UI 配線）とレイアウト DOM 構築（buildLayoutNode / applyPaneLayout / ドラッグ＆ドロップ）を独立モジュールへ切り出す。

### V1-13. removeLeaf が ratios の不変条件を型で守っていない（軽微・要確認）
- tools/formalization-viewer/src/layout-tree.ts（removeLeaf）
- 該当箇所: `ratios.push((node.ratios ?? [])[i]);`
- 問題点: 入力ノードの ratios が children より短い場合、ratios に undefined が混入したツリーを返す。validateTree を通した木では起きないが、addLeaf / removeLeaf / flattenSameDir の合成では「ratios は children と同長」という不変条件が暗黙のまま。
- 提案: ratios 欠落時は 1 を補う（validateTree 側の扱いに揃える）。

## アクセシビリティ

### V1-14. スプリッタがマウス専用でセパレータとしての意味付けがない
- tools/formalization-viewer/src/app.ts（buildSplitter）
- 問題点: スプリッタは mousedown ドラッグのみで、`role="separator"`、aria-valuenow、キーボード（矢印キー）での比率調整がない。ペインの表示切替や Columns/Rows プリセットはキーボードでも可能だが、比率調整だけがマウス必須になっている。
- 提案: スプリッタに `role="separator"` と tabindex=0 を与え、矢印キーで resizePair を駆動できるようにする。

### V1-15. About ダイアログにフォーカストラップがない
- tools/formalization-viewer/index.html:329 / tools/formalization-viewer/src/app.ts（openAbout / closeAbout）
- 問題点: `role="dialog" aria-modal="true"` を宣言し開く際に閉じるボタンへフォーカスを移すが、Tab キーでダイアログ背後の要素へ抜けられる。モーダルを名乗る以上、支援技術利用者には背後が操作不能である前提と食い違う。Escape で閉じられる点は良い。
- 提案: 簡易なフォーカストラップ（ダイアログ内のフォーカス可能要素で Tab を循環）を入れる。設定メニューも Escape で閉じられると一貫する（現状は外側クリックのみ）。

### V1-16. リストボックスのハイライトが支援技術に伝わらない
- tools/formalization-viewer/src/app.ts（renderMarkerList）、tools/formalization-viewer/src/select-dropdown.ts（buildList）
- 問題点: マーカーパレットとカスタムドロップダウンはどちらも role="listbox" / role="option" を持ち、視覚ハイライト（.is-highlight）を矢印キーで移動するが、aria-activedescendant がなく option に id もないため、スクリーンリーダーは現在のハイライト位置を知ることができない。
- 提案: option に安定した id を振り、コンボボックス側に aria-activedescendant をハイライト移動に合わせて更新する。

## その他（軽微）

### V1-17. peer ペインのラベルが英語固定
- tools/formalization-viewer/index.html（pdf-peer-pane-option の "English PDF"、pdf-peer-viewer の aria-label "English PDF preview"）
- 問題点: peer の表示名は manifest の label で差し替えられる箇所（pdf-peer-label）と、HTML に直書きの箇所（設定メニューの選択肢名と aria-label）が混在する。本プロジェクト（日本語版＋英語版 peer）では正しいが、汎用ビューアとしては peer 言語の決め打ちになっている。要確認。
- 提案: 設定側ラベルも manifest の parallelPdf.label から流し込む。

## 以上、指摘終わり

---

# 付録: バッチ V2

# バッチ V2: formalization viewer サーバ側（server/*.ts + e2e）

対象リビジョン: sunaemon/math-private @ 9d6e65df
対象: tools/formalization-viewer/server/ 配下の全 .ts（serve, projects, request-trust, lean-bridge, lean-server, process-group, free-port, file-watcher, book-builder, lsp-cache, static-dist, repo-version と各 .test.ts）、tools/formalization-viewer/e2e/ 配下の全 .ts。
総評: 設計意図はコメントで丁寧に説明され、セキュリティ境界（ループバック限定バインド、Host/Origin 検査、allowlist + realpath 再検査、make ターゲットへのコマンドインジェクション対策）も意識的に作られている。指摘は主に、検証の非対称、並行実行時の競合（要確認）、重複実装、テスト不足に集中する。重大な脆弱性は見つからなかった。

## セキュリティ

### V2-1. projects.ts:125-157 — manifest の `dir` フィールドが未検証
該当箇所: `validateManifest` は `lspDir` を `/^[A-Za-z0-9._-]+$/` で厳格に検証する一方、`dir` は型も形式もチェックせず、`readProject` は `meta.dir === undefined` のときだけディレクトリ名で補う。
問題点: `"dir": "../something"` や非文字列が manifest に入ると、`lspRoots` の構築や `path.join(root, meta.dir, ...)` の前提が崩れる。`lspDir` との検証レベルの非対称は、片方だけ将来の変更で緩む温床になる。manifest はローカル設定なので緊急度は低い。
提案: `dir` にも `lspDir` と同じ検証（トップレベル名のみ許可）を適用する。

### V2-2. serve.ts:239, 269 — serveStatic の realpath 検査と読み取りの間の TOCTOU（要確認・軽微）
該当箇所: `realPath = fs.realpathSync(fsPath)` で包含検査をした後、`fs.createReadStream(fsPath)` が元のパスを開き直す。
問題点: 検査とオープンの間にシンボリックリンクを差し替えられると検査をすり抜ける。相手は同一マシン上のプロセスに限られ、本サーバはループバック限定の開発ツールなので実害はほぼないが、検査が「realpath で得たパス自体を開く」形になっていない点は指摘しておく。
提案: `realPath` を createReadStream に渡す。

### V2-3. serve.ts:384-388 — readBody が宣言長超過時にリクエストを破棄しない
該当箇所: `if (!Number.isNaN(declared) && (declared < 0 || declared > limit)) { reject(...); return; }`（対してデータ受信中の超過時は `req.destroy()` する）。
問題点: Content-Length が上限超を宣言したクライアントは送信を続けるため、413 レスポンスが届かずソケットが残りうる。2つの超過経路で扱いが非対称。
提案: 宣言長超過時も `req.destroy()` する（413 を確実に返すならレスポンス送信後に destroy）。

### V2-4. serve.ts:498-503 — HEAD / が GET と異なる結果になる（軽微）
該当箇所: HEAD は一律に `applyMount` + `isAllowedPath` 経由で serveStatic に入り、GET の `/` → デフォルトマウントへの 302 リダイレクトを通らない。
問題点: `HEAD /` は allowlist 不一致で 403 になり、GET / の 302 と食い違う。監視・ヘルスチェック用途で混乱の元。
提案: HEAD でも GET と同じルーティング（リダイレクト・マニフェスト等）を通し、ボディだけ落とす。

### V2-5. serve.ts:455 / lsp-cache.ts（generate）— file:// URI の組み立てにエンコードがない（要確認・軽微）
該当箇所: `` rootUri: `file://${lspRoot}` ``、lsp-cache 側も `` `file://${projectRoot}` ``。
問題点: リポジトリパスに空白・`#`・`%` が含まれると URI が壊れ、LSP の rootUri が別パスを指す。チェックアウト先パスは利用者が選ぶため起こりうる。
提案: `url.pathToFileURL()` を使う。

## 正しさ

### V2-6. lean-bridge.ts:58-60, 117 — spawn 失敗時にブリッジが固まる可能性（要確認）
該当箇所: `running()` は `this.proc.exitCode === null && this.proc.signalCode === null` で判定し、spawn の 'error' は `announceClosed` に接続されるのみで `this.proc` は差し替わらない。
問題点: `lake` が PATH にない等で spawn が ENOENT になった場合、Node では 'exit' が発火せず exitCode が null のまま残ることがある。この場合 `running()` は true を返し続け、`ensure()` は二度と spawn せず、`send()` は壊れた stdin へ書き続ける。serve.ts のプロセスガードは ERR_STREAM_DESTROYED を握りつぶすため、症状は「無言で応答しないブリッジ」になる。
提案: 'error' ハンドラで該当 proc を無効化する（世代チェック付きで `this.proc = null` 相当）、もしくは running() に spawn 失敗フラグを併用する。実プロセスでの再現確認が望ましい。

### V2-7. lean-bridge.ts:124-156 — initialize の restart が send 間で直列化されていない（要確認）
該当箇所: `send()` は `isInitialize` のたびに `await this.restart()`（terminate → proc = null → spawnProcess）を行う。SessionRegistry の inflight カウンタは reaper からの保護専用で、send 同士の順序は保証しない。
問題点: 2つの POST /lsp/send が並行すると terminate/spawn が交錯し、先に spawn したサーバが `this.proc` の上書きで追跡対象から外れ、shutdown でも回収されない孤児プロセスになりうる。ブラウザ側は通常直列に送るため顕在化しにくい。
提案: ブリッジ単位で send を直列化する（単純な promise チェーンで十分）。

### V2-8. lean-bridge.ts:270-275 — 実行中ブリッジへの別プロジェクト root の送信が黙って旧 root に届く（要確認）
該当箇所: `if (root !== undefined && !bridge.running()) bridge.root = root;`
問題点: コメントは「lazy spawn 前の付け替え」を意図するが、ブリッジが既にデフォルト root で起動済みの場合、別プロジェクトを指定した send はエラーにもならず旧プロジェクトの Lean サーバへ送られる。セッション id をプロジェクト間で再利用するクライアントがあると、誤ったプロジェクトのゴール状態が返る。
提案: running 中に異なる root が来たら再起動するか、セッションと root の対応を registry 側で検証する。

### V2-9. lean-bridge.ts:86-118 / lean-server.ts:67-93 — LSP フレーミング解釈の重複と、負の Content-Length で前進しない解釈（要確認）
該当箇所: Content-Length ヘッダ解釈ループが両ファイルにほぼ同一で存在する。`length` が負の値だと `buffer.subarray(bodyStart, bodyStart + length)` と次バッファの切り出しが後退し、同じヘッダを再解釈し続ける。
問題点: 出力元はローカルの Lean サーバのみなので攻撃経路ではないが、不正なフレームで無限ループ（CPU 占有）になりうる。重複実装のため片方だけ直すドリフトも起きやすい。
提案: フレーミングを共有モジュールに切り出し、`length < 0` を malformed として扱う。

### V2-10. file-watcher.ts:88-97 — watchexec の異常終了を監視していない
該当箇所: spawn した watchexec には 'error' ハンドラのみで 'exit' ハンドラがない。`ensure()` は exitCode を見て再 spawn できるが、呼ばれるのは新規 SSE 購読時のみ。
問題点: watchexec がクラッシュすると、開いている全タブのライブリロードが無言で止まり、新しいタブを開くまで回復しない。
提案: 'exit' で `this.proc = null` にし、購読者が残っていれば再 ensure する。

### V2-11. book-builder.ts:44, 299-306 — デバウンスの説明（per-project）と実装（全体で単一タイマ）の不一致
該当箇所: 環境変数の説明は `BOOKLINK_AUTOBUILD_DEBOUNCE_MS  per-project debounce`、実装の `schedule()` は全プロジェクト共有の `this.timer` を毎回クリアして張り直す。
問題点: どれか1プロジェクトでも編集が続く限り、全プロジェクトのビルドが先送りされ続ける（starvation）。実用上は問題になりにくいが、説明と挙動が違う。
提案: 説明を「全体で1つのデバウンス」に直すか、タイマをプロジェクト（バッチ）単位の上限付き（最大待ち時間）にする。

### V2-12. static-dist.ts:210-211, 234 — `--dist` の再帰削除にガードがない
該当箇所: `if (fs.existsSync(dist)) fs.rmSync(dist, { recursive: true, force: true });`。dist の出所は `--dist` 引数そのままで、root 自身や root 外を指していないかの確認がない。値なしで `--dist` を渡すと `path.resolve(undefined)` の不親切な TypeError になる。
問題点: 引数の打ち間違いでリポジトリ自身や無関係なディレクトリを消す事故が起きうる。Makefile 経由の通常運用では固定パスでも、スクリプト単体実行時の安全弁がない。
提案: dist が root と同一でないこと、および（原則として）root 配下か専用名であることを削除前に検証する。引数値の欠落も明示エラーにする。lsp-cache.ts:335-350 の parseArgs も同様で、`--elab-timeout` の値欠落は NaN になり、 deadline 計算が NaN になってタイムアウトが効かなくなる。

### V2-13. lsp-cache.ts:317 — キャッシュ JSON の書き込みが非アトミック（要確認・軽微）
該当箇所: `fs.writeFileSync(outPath, JSON.stringify(cache))`。
問題点: 生成途中でプロセスが落ちると中途半端な JSON が残る。次回生成時は key 解析失敗として再生成されるので自己回復はするが、生成と dist コピーが重なると壊れたキャッシュが配布側に渡りうる。
提案: 一時ファイルに書いて rename する。

### V2-14. lsp-cache.ts:101-128 — cacheKey がファイルごとに推移閉包全体を再ハッシュする（性能・要確認）
該当箇所: `cacheKey()` は対象ファイルごとに import 閉包をたどり、全ファイルを SHA-256 する。generate は対象ファイル数だけこれを呼ぶ。
問題点: ファイル数 × 閉包サイズのオーダーで同じファイルを何度も読んでハッシュする。大規模プロジェクトでは生成前チェックが支配的になりうる。
提案: 閉包ハッシュをファイル単位でメモ化し、キー計算を共有する。

## 保守性

### V2-15. projects.ts:125 / static-dist.ts:77 — validateManifest・Manifest・walkFiles の重複実装
該当箇所: `validateManifest` が両ファイルに同一内容で存在し、`Manifest` インタフェースも static-dist.ts:37-46 で再定義されている。ディレクトリ走査も projects.ts の `walkFiles` と static-dist.ts の `walkFiles`、さらに lsp-cache.ts の `discoverLeanFiles` がよく似た別実装。
問題点: 検証規則（例: V2-1 の dir 検証）を直すときに片方だけ直るドリフトが起きやすい。実際、live サーバ側と dist 側で検証を揃える必要がある箇所である。
提案: validateManifest と Manifest 型は projects.ts から export して static-dist が共有する。走査も symlink 循環ガード付きの1実装に寄せる。

### V2-16. repo-version.ts:40-58 / serve.ts の sendManifest — リクエストごとの git 同期実行
該当箇所: `repoVersion()` は `execFileSync("git", ...)` を3回同期実行し、serve.ts は manifest リクエストのたびにこれと `attachLicenseText`（ファイル読み込み）を呼ぶ。
問題点: 同期子プロセス起動がイベントループをブロックする。値はプロセスの生存中は不変（作業ツリーの dirty 状態だけが変わりうる）なので、毎回の再計算は無駄が大きい。
提案: 起動時に一度だけ計算してキャッシュする（dirty 判定を捨てるか、manifest 応答の鮮度要件があるなら短い TTL を付ける）。

### V2-17. テスト不足 — セキュリティ境界そのものに単体テストがない
該当箇所: projects.test.ts は「翻訳プロジェクトが他プロジェクトの Lean root を共有できる」1件のみ（28行）。request-trust.test.ts と lean-bridge.test.ts は対象を絞った良いテストがあるが、`isAllowedPath` / `applyMount` のパストラバーサル境界、serve.ts のルーティング、file-watcher、lsp-cache、static-dist には単体テストがない。
問題点: allowlist と mount 書き換えはこのサーバの実質的なセキュリティ境界であり、回帰が最も起きてほしくない箇所。現状は e2e（実ブラウザ）でしか守られていない。
提案: projects の isAllowedPath/applyMount に対する表形式テスト（`..`、%2e エンコード、二重スラッシュ、flat 制限、拡張子ケース）を追加するだけでも価値が高い。

### V2-18. static-dist.ts:95-113 — dist は複数プロジェクトのうち最初の1件だけを対象にする（要確認）
該当箇所: `loadProject` は候補の先頭1件を返して終わる。一方 serve.ts は全プロジェクトを同時マウントする。
問題点: BOOKLINK_PROJECT を指定しないと、ソート順で最初のプロジェクトだけが dist に入り、他は無言で落ちる。意図的な単一プロジェクト配布なら、その旨と選択方法を冒頭コメントに明記すべき（現コメントは "one URL tree" と単数形だが、他プロジェクトが除外されることは読み取りにくい）。
提案: 意図的ならコメントと README に明記。そうでなければ全プロジェクト分のツリーを出す。

### V2-19. static-dist.ts:30, 236-246 — dist に e2e や fixtures 等のビルド専用物もコピーされる（軽微）
該当箇所: `VIEWER_EXCLUDE` は `src` と `server` のみで、viewer ディレクトリを丸ごと cpSync する。
問題点: e2e/（TypeScript のテストソース）、fixtures/、tsconfig 等が配布物に混ざる。サイズと情報露出の両面で小さな無駄。
提案: 除外集合に e2e、fixtures を加えるか、配布に必要な物の allowlist 方式にする。

### V2-20. repo-version.ts:131-145 — katexMacros の括弧数えがエスケープを考慮しない（要確認・軽微）
該当箇所: `readBraced` は `{`/`}` を素朴に数える。
問題点: マクロ本体に片方だけの `\{` または `\}` が含まれると深さがずれ、本体の切り出し位置がずれて誤った KaTeX マクロになる。macros.tex の実データで顕在化するかは未確認。
提案: バックスラッシュでエスケープされた括弧を数えない。対象 macros.tex に該当パターンがあるか grep で確認してから直すとよい。

### V2-21. e2e/viewer-server.ts:16-45 — stop() がサーバ終了を待たず、起動失敗時の診断も出ない（軽微）
該当箇所: `stop` は SIGTERM を送るだけで終了を待たない。`stdio: "ignore"` のため起動失敗時は util の waitForHttp が汎用タイムアウトを投げるのみ。
問題点: serve.ts の終了処理（最大15秒の failsafe 付き）が終わる前にテストプロセスが先行し、次の実行や残存 Lean プロセスと競合しうる。失敗時の原因も追いにくい。
提案: stop を非同期化して 'exit' を待つ。サーバの stderr は少なくとも起動失敗時に表示できるようバッファする。

### V2-22. server/free-port.ts と e2e/util.ts — 空きポート取得の重複実装（軽微）
該当箇所: `usablePort`（free-port.ts）と `freePort`（e2e/util.ts）が同じ「bind して閉じて返す」処理を別々に持つ。
問題点: 小さい重複だが、競合窓への対処方針（片方はコメントで明示）が揃っていない。
提案: e2e 側も free-port.ts の実装を使う。

## 確認して問題なかった点

- バインドは 127.0.0.1 のみ（serve.ts:558）。Host/Origin 検査（request-trust.ts）は DNS リバインディングとクロスオリジン POST を意識した実装で、テストも主要ケースを押さえている。
- 静的配信は allowlist（projects.isAllowedPath）+ serveStatic 内の語彙的検査と realpath 再検査の多層で、コメントにある通りシンボリックリンク経由の脱出も塞いでいる。
- book-builder の make ターゲットは、クライアント申告の選択パスから章名を `/^[A-Za-z0-9_-]+$/` で検証してから組み立てており、コメントで説明されたコマンドインジェクション対策がテスト（book-builder.test.ts）付きで実装されている。BOOKLINK_MAKE もシェルを介さない単一プログラム名として実行される。
- プロセス終了は process-group.ts のグループ kill（SIGTERM→SIGKILL）で lake→lean の子孫まで回収する設計で、serve.ts の shutdown にも 15 秒 failsafe がある。
- lean-bridge.test.ts は reaper と send の競合契約をスタブで再現する良いテストで、本レビューで要確認とした並行系の指摘はその対象外（send 同士、spawn 失敗時）に限られる。

## 以上、指摘終わり

---

# 付録: バッチ B1

# バッチ B1: ビルド基盤・CI レビュー（sunaemon/math-private @ 9d6e65df）

対象: setup.sh / tools/setup_codex.sh / tools/worktree_caches.sh /
tools/install_codex_debian.py /.github/workflows/check.yml / lefthook.yml /
mise.codex.toml /.devcontainer/devcontainer.json / lint 設定群
（.hlint.yaml /.oxlintrc.json / ruff.toml / fourmolu.yaml /
.prettierrc.json /.coderabbit.yaml /.gitattributes）。

総評: 全体にコメントで設計意図が明示され、冪等性・失敗時の扱いも丁寧。
CI はアクションを SHA でピン留めし権限も最小（contents: read）。
codex 側はダウンロードに SHA256 ロックを課すなど水準が高い。
以下はその水準から見た残りの不整合・穴である。

## setup.sh

### B1-1. dry-run が Perl モジュール未導入環境で exit 1 する（cpanm の有無で挙動が変わる）

- setup.sh:997-1013 / `run_cmd "${cpanm}" --notest --local-lib...` の直後に
`if! perl_modules_available; then... exit 1; fi`
- 問題点: システムに cpanm がある場合、dry-run では run_cmd は印刷のみで
実際にはインストールされないため、直後の実在チェック
perl_modules_available が必ず失敗し、`--dry-run`（= `make setup` の
プレビュー）が exit 1 で終わる。cpanm が無い場合は elif 分岐で早期
return して成功するので、dry-run の成否が cpanm の有無という無関係な
条件に依存する不整合がある。
- 提案: 最終検証を `[[ "${DRY_RUN}" -eq 0]]` で囲むか、cpanm 分岐でも
dry-run 時は検証前に return する。

### B1-2. rm -rf の対象が環境変数由来のパスで、範囲ガードがない

- setup.sh:582 / `rm -rf "${TEXLIVE_INSTALL_ROOT}"`
- setup.sh:991 / `run_cmd rm -rf "${PERL_LOCAL_LIB}"`
- 問題点: 両変数とも環境変数で上書き可能（TEXLIVE_ROOT /
TEXLIVE_INSTALL_ROOT / PERL_LOCAL_LIB）。誤った値（例: `/` や
ホームディレクトリ）を渡すと、そのまま削除対象になる。現在の
ガードは `-d` チェックのみで、「リポジトリ配下（${PWD} 配下）の
パスであること」「空でないこと」の確認がない。
- 提案: 削除前に `case "${path}" in "${PWD}"/*)` 等で配下チェックを入れ、
外れたら中断する。install_codex_debian.py 側の作法（チェックサム
不一致時に「自分で消して再試行」と案内し自動削除しない）とも
方向が揃う。

### B1-3. install_mise_linux の curl は dry-run でも実際にダウンロードする

- setup.sh:889 / `if! curl -fsSL https://mise.run -o "$mise_installer"...`
- 問題点: 「コマンドを印刷するだけ」が dry-run の契約だが、この curl は
run_cmd を経由せず実ネットワーク取得を行う（テンポラリファイルへの
書き込みと削除も伴う）。add_texlive_host_platform や
install_repo_texlive の dry-run 分岐が厳密にガードされているのと
対照的で、一貫性を欠く。
- 提案: dry-run 時はダウンロードを模擬表示に切り替える（現状の
インストーラ取得可否の事前確認が目的なら、その旨をコメントに明記）。

### B1-4. install-tl アーカイブ自体に完全性検証がない

- setup.sh:587-595 / `curl -fsSL "$(texlive_install_url)" -o "${archive}"`
→ そのまま展開して `"${installer}" -profile...`（623行）を実行
- 問題点: 凍結スナップショットからの取得とはいえ、install-tl 本体
（実行されるコード）のチェックサム／署名検証がない。パッケージ側は
tlpdb のチェックサムで守られるが、インストーラ自体が入口になる。
codex 側（install_codex_debian.py、setup_codex.sh）が全ダウンロードに
SHA256 を課しているのと水準が揃っていない。
- 提案: スナップショット日付に対応する install-tl の SHA256 を
スクリプトに固定する（TLMGR_REPOSITORY 上書き時は検証を任意化）。

### B1-5. cpanm スクリプトを検証なしにダウンロードして実行する

- setup.sh:1005-1006 / `run_cmd curl -fsSL -o "${workdir}/cpanm" "${CPANM_URL}"`
の後に `perl "${workdir}/cpanm" --notest...`
- 問題点: https://cpanmin.us から取得したスクリプトをそのまま Perl で
実行し、CPAN モジュールも署名検証なし・--notest で入る。mise.run の
浮動インストーラについては行879-883のコメントで既知の例外として
明示されているが、cpanm 側には同様の注記も検証もない。
- 提案: cpanm の SHA256 固定、または既知の例外である旨のコメント追加。

### B1-6. TLMGR_REPOSITORY=ctan のとき URL 変換と生値の受け渡しが混在する

- setup.sh:623 / `"${installer}" -profile "${profile}" -repository "${TLMGR_REPOSITORY}"`
- setup.sh:1021 / `run_tex_cmd tlmgr option repository "${TLMGR_REPOSITORY}"`
- 問題点: texlive_install_url（543-549行）と texlive_repository_url
（442-449行）はキーワード `ctan` を mirror.ctan.org の URL に変換
するが、上記2箇所は生の `ctan` を install-tl / tlmgr に渡す。
tlmgr が `ctan` を特別扱いするかは未確認で、片方だけ変換する現状は
少なくとも一貫しない。
- 提案: 両箇所とも texlive_repository_url の出力を渡す。

### B1-7. install_translation_tools のコメントと実体のずれ

- setup.sh:954-957 のコメント / 「provisions... GNU gettext and
po4a's CPAN Perl modules」
- 問題点: 実体は install_perl_modules の呼び出しのみで、gettext は
mise（conda:gettext-tools）が担う（ヘッダコメント行20-23と
mise.toml の記述が正）。このコメントだけ読むと gettext の供給元を
誤解する。
- 提案: コメントを「gettext は mise 側、本関数は CPAN モジュールのみ」
に修正。

### B1-8. macOS で build basics（cc/make）の事前確認がない

- setup.sh:842-864（install_macos）/ 914-951（install_linux は
LINUX_BUILD_BASICS で確認）
- 問題点: Linux 側は cc/make/curl/git の有無を確認してから進むが、
macOS 側は mise の導入のみで、Xcode Command Line Tools が無い環境
でもそのまま進み、Syntax::Keyword::Try（XS）のコンパイル段階で
初めて分かりにくい失敗になる。doctor にも cc のチェックがない。
- 提案: install_macos と doctor に `cc`/`make` の存在チェックを追加。

##.github/workflows/check.yml

### B1-9. ジョブに timeout-minutes がなく既定の360分

-.github/workflows/check.yml:31-（jobs.check 全体）
- 問題点: lint + test + 全 Lean ビルド + dist 構築という高コスト
ジョブで、ハングした場合は GitHub 既定の6時間までランナーを
占有する。concurrency の cancel-in-progress は「次の push が来た
場合」にしか効かない。
- 提案: 実績に余裕を持たせた timeout-minutes（例: 180）を明示する。

### B1-10. セットアップキャッシュのキーが OS イメージ世代を区別しない

-.github/workflows/check.yml:53-62, 97-107 /
`key: setup-${{ runner.os}}-${{ hashFiles('mise.toml', 'lean-toolchain', 'setup.sh')}}`
- 問題点: runner.os は "Linux" 固定で、ubuntu-latest のメジャー更新
（Perl ABI や glibc の変化）をキーに反映しない。旧イメージで作った
.perllib / ~/.elan / mise ツリーが新イメージに復元されうる。
.perllib は setup.sh 側のロード可否検出で自己修復するが、CI は
`make doctor` を実行しないため、他ツリーの不整合は lint/test の
失敗として初めて現れる。
- 提案: キーにイメージ識別子（例: `$(lsb_release -rs)` 相当や
ImageVersion 環境変数）を含めるか、プロビジョニング後に
`./setup.sh --doctor` を1ステップ追加する。

## tools/setup_codex.sh / tools/install_codex_debian.py

### B1-11. mise 本体の検証が同一リリースの SHASUMS256.txt 依存

- tools/setup_codex.sh:112-115 / ターball と SHASUMS256.txt を同じ
GitHub リリースから取得して照合
- 問題点: リリース自体が差し替えられた場合に検出できない一段弱い
検証で、elan（133行）と Lean（147行）がスクリプト内ハードコードの
SHA256 を使う方式と揃っていない。
- 提案: mise も期待 SHA256 をスクリプトに固定する（バージョン
バンプ時に3箇所同時更新になる点はコメントで明示）。

### B1-12. install_codex_debian.py が使う dpkg-deb が前提一覧にない

- tools/install_codex_debian.py:58 / `subprocess.run(["dpkg-deb", "--extract",...])`
- tools/setup_codex.sh:63-68 の前提コマンド一覧に dpkg-deb が含まれない
- 問題点: 対象イメージには当然入っている前提だが、一覧にある他の
ツールと扱いが不統一で、欠けた環境では Python のトレースバックで
落ちて原因が伝わりにくい。
- 提案: 前提一覧に dpkg-deb を追加する。

## 設定ファイル群

### B1-13..devcontainer のイメージが浮動タグ

-.devcontainer/devcontainer.json:3 /
`"image": "mcr.microsoft.com/devcontainers/base:ubuntu"`
- 問題点: mise.toml の全ツールピン留め、codex の SHA256 ロックと
いう本リポジトリの再現性方針の中で、devcontainer のベース
イメージだけが無タグ（=latest 相当）で、再構築のたびに中身が
変わりうる。
- 提案: 少なくともリリースタグ（例: base:ubuntu-24.04）を固定し、
可能ならダイジェストも併記する。

### B1-14. mise 本体のバージョンの出所が3系統に分かれている

- ローカル: setup.sh は既存の mise を無検証で使用（doctor も
バージョンを確認しない）
- CI:.github/workflows/check.yml:76 の mise-action 同梱版
- codex: tools/setup_codex.sh:111 で 2026.10.19 に固定
- 問題点: mise.toml は管理対象ツールの版は固定するが mise 自体は
固定しておらず、環境ごとに異なる mise で `mise install` が
走る。mise の挙動差（バックエンド解決など）が環境差異の原因に
なりうる。
- 提案: doctor に想定 mise バージョン範囲のチェックを足すか、
少なくとも想定バージョンを README/setup.sh に明記する。

### B1-15. ruff.toml の per-file-ignores が指すファイルの現行存在が未確認

- ruff.toml:7-10 / `"tools/worktree_diff.py" = ["E402"]`
- 問題点: 今回レビューしたファイル群に tools/worktree_diff.py が
含まれておらず、現行ツリーに存在しないなら陳腐化した設定
（実害はないが、設定の棚卸し対象）。
- 提案: 実ファイルの有無を確認し、無ければエントリを削除する。

### B1-16. worktree_caches.sh の複製チェックと実行の間に競合の余地

- tools/worktree_caches.sh:158-176 / `[[ -e "${dst}"]] && continue`
の後に cp を実行
- 問題点: setup.sh 冒頭でも自動実行されるため、`make worktree-caches`
や別セッションの setup と同時実行されると、存在チェックを通過した
2プロセスが同じ dst へ同時に cp しうる（片方が rm -rf して再試行
する経路もある）。キャッシュの破損は再生成可能なので実害は
小さいが、同時実行を想定した排他がない。
- 提案: 先行プロセスが作りかけの dst を検出できるよう、一時名へ
コピーしてから rename する、もしくは簡易ロックを取る。

以上、指摘16件（中2件、低12件、要確認2件）。
lefthook.yml、mise.codex.toml、.hlint.yaml、.oxlintrc.json、
fourmolu.yaml、.prettierrc.json、.coderabbit.yaml、.gitattributes
については、意図がコメントで明示されており指摘なし。

## 以上、指摘終わり

---

# 付録: バッチ T1

# テストコードレビュー T1（sunaemon/math-private @ 9d6e65df、tests/ の Python テスト群）

観点: (1) 各テストが守るものとカバレッジの穴 (2) 壊れやすさ (3) 実装の複製・自己参照 (4) 保守性。原稿本文は対象外。

## 概要：各テストファイルが守っているもの

- `tests/test_booklink_sourcemap.py`: booklink マーカー解析、Lean 宣言の検出、抜粋と本文の照合（空白改行に鈍感な一致、シンボリックリンク越しでも book-local なパスを保つこと）、tex スパンとの順序どおりの対応付け、skip 区間の解析。
- `tests/test_booklink_coverage.py`: 形式化スコープの判定（covered/uncovered/partial/exempt）、`formalization:` 注釈の意味論、skip とアンカーの矛盾の検出、同一宣言への target 重複の検証。
- `tests/test_booklink_audit.py`: 証明ギャップの集計で「リンク済み」が「証明済み」に化けないこと、レビュー決定の失効（passage/evidence のハッシュ変化）、scope review が元データを書き換えないこと。
- `tests/test_translation_structure.py`: 日英の構造一致（見出し・ラベル・引用・数式・用語同一性・mathmeta・順序）、コードフェンスやコメントの除外、診断メッセージの出し方と CLI の終了コード。
- `tests/test_translation_workflow.py`: PO→生成 Markdown の検証付きインストール（全章アトミック性、unchanged のとき mtime を保つ、symlink への書き込み拒否、読み取り専用チェック）、translation-status の sourceBlob 陳腐化検出。
- `tests/test_translation_terms.py`: 用語集ルールの適用（文脈依存の可否、定義キー検査、レンダリングされない範囲の除外、PO 内の位置報告）、用語集スキーマの検証、本書の実用語集に対する文脈回帰。
- `tests/test_translation_sourcemap_projection.py`: PO パース、文単位の精密化（アンカー multiset 一致時のみ）、メッセージ単位へのフォールバック、共有範囲の統合、statement と prose/proof の混在拒否、パス書き換え。
- `tests/test_validate_book_build.py`: TeX ログ診断の分類（本物の警告とメタデータ行の区別）、最終パスのログだけを見ること、古い PDF で失敗を誤魔化さないこと、index の digest 照合、本の発見。
- `tests/test_book_build_recovery.py`: 本物の Makefile テンプレート＋偽ツールでの統合検証。失敗した生成物の削除と再試行、warm aux の扱い、debug の索引リフレッシュ。
- `tests/test_raw_citations.py`: raw TeX 内の引用が citeproc に届くこと、対象外リテラル（コメント・verbatim・数式内）が引用化されないこと、AMS 書誌が日英で同一になること。
- `tests/check_notation_index.py`: 実 LuaLaTeX＋makeindex での統合チェック。記号索引キーが通常文・強調・定理タイトルで同一エントリに合流すること。

総じて単体テストの質は高く、境界ケース（弱い一致を covered にしない、skip とアンカーの矛盾など）の押さえは丁寧である。以下は残る穴と壊れやすさの指摘。

## A. カバレッジの穴

### A-1. テストが一切ない tools が複数ある
- 対象: tools/books_mk.py:36（`def main`）ほか tools/po_diff.py、tools/prepare_pandoc_templates.py、tools/split_skip_blocks.py、tools/validate_afk_chart_limit.py
- 問題点: `grep` で確認した範囲では、tests/ の全 Python テストのどこからも参照がない。特に `books_mk.py` は Makefile の本の発見（BOOKS 解決）に効く生成器で、壊れると全ビルド対象の選択が狂う。`prepare_pandoc_templates.py` も Pandoc テンプレート準備というビルド前段を担う。要確認：Haskell 側や CI の別経路で守られている可能性はあるが、Python テスト群の範囲では無防備。
- 提案: 最低限、代表入力に対する決定的な出力（生成される make 断片、テンプレート配置）を固定するスモークテストを追加する。

### A-2. 主要ツールの CLI `main` が未検証
- 対象: tools/booklink_sourcemap.py:893、tools/booklink_coverage.py:551、tools/booklink_audit.py:361、tools/project_translation_sourcemap.py:555、tools/check_translation_terms.py:236、tools/check_translation_workflow.py:259（いずれも `def main`）
- 問題点: ライブラリ関数は手厚くテストされているが、引数解析・入出力ファイルの受け渡し・終了コードという接着層はテストされていない。`test_translation_structure.py` と `test_validate_book_build.py` は `main` を呼んでおり、同じ流儀で守れることが実証されているのに、残りは素通りしている。Makefile から呼ばれるのは `main` 側なので、接着層の退行は実ビルドで初めて出る。
- 提案: 各ツールに「最小フィクスチャで main を呼び、終了コードと出力ファイルの有無を見る」テストを1件ずつ追加する。

### A-3. `check_translation_workflow` の実物検証関数が常にモックされている
- 対象: tests/test_translation_workflow.py:107 / `patch.object(checker, "_compare_message_sets") as compare_catalogs,`
- 問題点: `check_workflow` のテストでは `_compare_message_sets` と `_check_catalogs`（実 po4a 連携を含む）が全ケースで差し替えられ、実物の PO メッセージ集合比較は一度も走らない。守られているのは「呼び出し回数と順序」という配線だけで、比較ロジック自体の退行（メッセージの取りこぼし、並び替えへの感度など）は検出できない。`project_translation_sourcemap.read_po` のテストは別モジュールのパーサであり、こちらは代替にならない。
- 提案: 小さな実 PO/POT フィクスチャで `_compare_message_sets` と `_check_catalogs` を実物で通すテストを追加する。

### A-4. `validate_book_build.run_make` の実物が未検証
- 対象: tests/test_validate_book_build.py:111-117 / `def fake_make(self, text, code=0):`
- 問題点: 全テストが `run_make` を `fake_make` に差し替えており、tools/validate_book_build.py:89-100 の実物（make の起動、ログへのリダイレクト、所要時間の記録）は一度も実行されない。`test_book_build_recovery.py` は make を直接叩くが、`run_make` 経由ではないため、例えばログパスの渡し間違いや引数の組み立てミスは検出できない。
- 提案: 一時ディレクトリに自明な Makefile を置き、`run_make` 実物で成功・失敗の2ケースを確認するテストを追加する。

### A-5. `enable_booklink_highlight.py` の実物が空ファイルで置換されている
- 対象: tests/test_book_build_recovery.py:52 / `(self.root / "tools/enable_booklink_highlight.py").write_text("")`
- 問題点: 統合テスト内では空スタブにされ、他のテストからも参照がない。debug 用 .tex 生成に効く変換（booklink ハイライト注入）の退行は、どのテストでも検出できない。要確認：golden テスト（Haskell 側）が間接的に守っている可能性はある。
- 提案: 入力 .tex 断片に対する変換結果を固定する単体テストを追加する。

### A-6. `discover_books` のテストは公開抜粋の形だけ
- 対象: tests/test_validate_book_build.py:190-205 / `test_discovery_works_with_only_public_excerpt`
- 問題点: 発見ロジックの検証が JSON マニフェスト1形式のみで、私家版の全書マニフェスト（複数 stem・複数書籍が並ぶ形）での発見は未検証。要確認：マニフェスト形式が単一なら問題は小さいが、複数書籍の列挙順や重複 stem の扱いはこの形では守れない。
- 提案: 2書籍分のマニフェストを持つフィクスチャで発見結果（辞書全体）を固定するケースを追加する。

## B. 壊れやすさ（環境・順序・データ依存）

### B-1. 用語テストが本番用語集と Pandoc 実行環境に依存している
- 対象: tests/test_translation_terms.py:139-141 / `cls.glossary = checker.load_glossary(REPO_ROOT / "polish-space-ja/l10n/glossary-ja.yaml")`
- 問題点: `ContextualTerminologyTest` は本書の実用語集そのものを読み込み、その現在の政策内容（分裂／分割の区別など）をテストとして固定している。用語集は校閲のたびに変わる運用データなので、用語政策の正当な変更でテストコード側の修正まで必要になる（テストとデータの責務が混ざっている）。さらに tests/test_translation_terms.py:219-222 は `len(glossary.rules) > 30` と「一意化」の存在まで本番データに依存する。加えて `load_glossary` は tools/check_translation_terms.py:157-160 で `pandoc` をサブプロセス起動するため、Pandoc のない環境ではクラス setup で全滅する（skip ではなくエラー）。要確認：公開版リポジトリ（polish-space-ja の構成が異なる）でこのテストがどうなるかは未確認。
- 提案: 文脈ルールのテストは最小の合成用語集に寄せ、本番用語集への結合は「読み込めて件数が0でない」程度のスモークに分離する。Pandoc 不在時は `skipUnless(shutil.which("pandoc"))` で明示的にスキップする。

### B-2. raw citations テストは未ビルド環境で無言で全スキップされる
- 対象: tests/test_raw_citations.py:18 / `@unittest.skipUnless(shutil.which("pandoc") and FILTER.is_file(), ...)`
- 問題点: `build/book-filter` が存在しない環境（cabal ビルド前の新チェックアウト、CI のジョブ分割ミス）ではクラス全体がスキップされ、緑のまま引用パイプラインの退行を見逃す。スキップ自体は妥当だが、「ビルド済みであるべき CI 文脈では必須」という区別がない。
- 提案: 環境変数（例：CI）がある場合は skip ではなく fail にする、あるいは Makefile のテストターゲット側で book-filter のビルドを前提依存にする。

### B-3. raw citations テストが本番 references.bib の文字列を固定している
- 対象: tests/test_raw_citations.py:101-109 / `self.assertIn(r"J. Amer. Math. Soc. \textbf{3} (1990), no. 4, 903--928", bibliography)`
- 問題点: Kechris1995 等の実エントリの誌名・ページ・報告番号（C-145、機関名）を期待値に埋め込んでいるため、参考文献の正当な修正（誤記の訂正など）でフィルタと無関係なテストが落ちる。golden 的な回帰固定としては意図的とも読めるが、守りたい対象（citeproc の透過性・言語間同一性）に対して固定範囲が広すぎる。
- 提案: 検証用の最小 .bib フィクスチャを用意し、本番 bib への依存は「両言語で同一」という相対比較だけに絞る。

### B-4. recovery テストが本番 Makefile を文字列検索で切り出している
- 対象: tests/test_book_build_recovery.py:61-66 / `start = source.index(f"define {name}\n")`
- 問題点: `define book-dir-rules` の出現位置に依存し、Makefile 側の整形（define の前後のコメント追加や空白の変化）で `ValueError` によるテストエラーになる。失敗の仕方が「アサーション失敗」ではなく「テスト基盤の崩壊」なので、退行の切り分けがしにくい。また同ファイル:108-118 の `make` 起動には存在チェックや skip がなく、GNU make のない環境では同様に基盤ごと落ちる（raw citations 側には skipUnless の流儀があるのに揃っていない）。
- 提案: 切り出しに失敗したら対象テンプレート名を含む明示的なメッセージで fail させる。`make` は `skipUnless(shutil.which("make"))` でガードする。

### B-5. validate テストの陳腐化判定がナノ秒 mtime の粒度に依存している
- 対象: tests/test_validate_book_build.py:69-70 / `os.utime(path, ns=(2_000_000_000, 2_000_000_000))`、同:102-103 の `ns=(3_000_000_000, ...)`
- 問題点: 「tex より pdf が古い」等の前後関係を 1 秒刻みの人工タイムスタンプで作っている。タイムスタンプ粒度が粗いファイルシステムや、utime の ns 指定を丸める環境では前後関係が潰れてフレーク化しうる。要確認：CI（Linux ext4/APFS）では問題ないはずだが、再現条件が環境依存である点は残る。
- 提案: 時刻差を大きく取る（例：基準を現在時刻から十分離す）か、比較対象のファイルだけを狙って順序を作る。

### B-6. structure テストが診断文字列の接頭辞と非公開関数に結合している
- 対象: tests/test_translation_structure.py:104-108 / `any(item.startswith(category) for item in diagnostics)`、同:172 / `checker._normalize_math(before)`
- 問題点: 診断カテゴリ名の文言変更（"headings" の改名など）で、動作が正しくてもテストが落ちる。カテゴリ名の一覧自体もテスト側の辞書（同:93-103）に複写されている。また `_normalize_math` は非公開 API で、リファクタリングで改名するとテストが追随を強いられる。
- 提案: 診断を文字列でなくカテゴリを表す構造化された値（列挙型やタプル）で返すよう寄せ、テストはそれを見る。非公開関数の直接テストは、公開経路（compare_texts）経由のケースに置き換える。

### B-7. projection テストが非公開関数と作業ディレクトリ依存の絶対パスに結合している
- 対象: tests/test_translation_sourcemap_projection.py:29-33 / `projection._anchors(...)`、同:96,126 の `projection._sentence_spans(...)`、同:138-139 / `Path("english/src/chapter.md").absolute()`
- 問題点: `_anchors`・`_sentence_spans` は非公開 API で、内部分割の方針が変わるとテスト側の期待値計算まで壊れる。また `.absolute()` は実行時の cwd で解決されるため、`/tmp` がシンボリックリンクな環境（macOS の /private/tmp 等）では `.resolve()` を使う別テスト（同:201）と正規化の前提がずれうる。要確認：現行 CI で実際にずれるかは未確認。
- 提案: 非公開関数の検証は `project_span` の結果経由に寄せ、パスは両テストとも `resolve()` に統一する。

### B-8. coverage テストが被テストモジュールの内部 import 別名をモックしている
- 対象: tests/test_booklink_coverage.py:40 / `mock.patch.object(cov.bk, "build_combined_sourcemap", return_value=sm)`
- 問題点: `cov.bk` は tools/booklink_coverage.py:60 の `import booklink_sourcemap as bk` という内部別名で、import の書き方を変えるだけでテストが壊れる。モック境界が「外部依存」ではなく「自モジュールの参照名」に置かれている。
- 提案: テスト用の入力（entries）を組み立てるコンストラクタを実装側に用意するか、モック対象を `booklink_sourcemap.build_combined_sourcemap` 自体に寄せる。

### B-9. sourcemap テストのシンボリックリンク前提
- 対象: tests/test_booklink_sourcemap.py:161-162, 197-198 / `alias.symlink_to(lean)`、`(excerpt / "lean").symlink_to(...)`
- 問題点: ディレクトリ・ファイルへの symlink 作成を無条件に行っており、symlink に権限が要る環境（Windows の非管理者実行など）では setup で落ちる。要確認：現在の CI が POSIX 前提なら実害はない。
- 提案: symlink 作成を try/except で包み、作れない環境では該当ケースだけ skip する。

### B-10. audit テストの絶対パス固定
- 対象: tests/test_booklink_audit.py:107 / `root = Path("/repo")`
- 問題点: 実在しない絶対パスを root に使っており、`statement_selector_issues` がパス文字列の処理だけで完結する現行実装では通るが、将来 root 配下の実ファイルを読むようになると環境依存の失敗になる。意図（実ファイルに触らない）も読み取りにくい。
- 提案: TemporaryDirectory 配下のパスに置き換え、「実ファイルは作らない」ことをコメントで明示する。

## C. 実装の複製・自己参照

### C-1. `git_blob_hash` の「現行 blob」テストが実装自身で期待値を作っている
- 対象: tests/test_translation_workflow.py:61 / `source_blob = checker.git_blob_hash(source)`
- 問題点: `test_status_loads_current_source_blob` は、検証対象の `git_blob_hash` で計算した値を status に書き込み、それが受け入れられることを確認しているだけなので、ハッシュ方式そのものが間違っていても（例：blob ヘッダの付け忘れ）両側が同じ誤りで一致し、テストは通る。独立した期待値があるのは空ファイルの既知ベクトル（同:21-28）だけで、非空ファイルの既知ベクトルがない。
- 提案: 非空内容について `git hash-object` の実出力（または既知の blob ID）を固定したケースを追加する。

### C-2. validate テストの index digest フィクスチャが実装のハッシュ方式を複写している
- 対象: tests/test_validate_book_build.py:66 / `".index-sha256": hashlib.sha256(b"index entry").hexdigest().encode()`
- 問題点: 「`.idx` の sha256 を `.index-sha256` に記録する」という被検証側の方式を、テストのフィクスチャ生成がそのまま再実装している。方式変更時にテストと実装を同時に直す必要があり、フィクスチャが「仕様」ではなく「実装の写し」になっている。検証したいのは digest の再計算一致そのものなので影響は小さいが、方式の正しさ自体はどこでも検証されていない。
- 提案: digest の中身ではなく「idx を変えると stale になる／変えなければ通る」という振る舞いに寄せ、ハッシュ方式の固定は専用の小さなテストに分ける。

### C-3. recovery テストの FAKE_TOOL が索引ツールの契約をミニチュア再実装している
- 対象: tests/test_book_build_recovery.py:15-40 / `FAKE_TOOL`（特に index モードと `-debug` 時の "missing destination" 判定）
- 問題点: 偽 latex/index は「idx を ind に写す」「ind が idx と一致しなければ警告ログを出す」という、refresh_debug_pdf と makeindex の契約の要約を再実装している。実物の収束条件や警告条件が変わると、偽物の世界ではテストが緑のまま実物だけが壊れる（あるいは逆）という乖離が起きる。統合テストの性質上フェイク自体は妥当だが、契約の出所がテスト内にしかない。
- 提案: 偽物が前提にしている契約（どのファイルがどの条件で再生成されるか）を、実物 docstring への参照コメントで明示し、実物の条件変更時にテスト側も見るべき箇所が分かるようにする。

### C-4. raw citations テストの AST 再構成が Pandoc の意味論をテスト側で再実装している
- 対象: tests/test_raw_citations.py:52-68 / `def reconstruct(value):`
- 問題点: Cite / RawInline / RawBlock の扱いをテスト側で歩いて再構成しており、期待値も元のソース文字列への置換で作っている。Pandoc の JSON AST 形状がバージョンで変わると、製品でなくテスト側が壊れる。mise で Pandoc がピン留めされている間は実害が小さいが、フィルタの退行とテスト基盤の退行の切り分けがしにくい。
- 提案: 再構成は「Cite の出現位置と ID 列」だけに絞り、本文の完全一致は citeproc 側の最終出力（latex）での検証に寄せる。

## D. 保守性

### D-1. booklink マーカー記法のフィクスチャが3ファイルに重複している
- 対象: tests/test_booklink_sourcemap.py:24-33 / `LEAN_MARKER`、tests/test_booklink_coverage.py:259-266 / `def _marker(...)`、tests/test_booklink_audit.py:14-28（entry 辞書の手組み）
- 問題点: `/-@ booklink:` の記法（キー名、excerpt のブロック形式）がテストごとに独立に書き直されている。マーカー仕様の変更時に、直すべき場所が少なくとも3か所に散らばり、直し漏れが「一部テストだけ古い仕様を守る」形で残る。
- 提案: マーカー文字列を組み立てる共通ヘルパーを tests 内の共有モジュール（または各ファイルが import できる小さな fixture 関数）に寄せる。

### D-2. `sys.path` への tools 追加の流儀がファイルごとに異なる
- 対象: tests/test_booklink_sourcemap.py:18-19 / `REPO_ROOT = os.path.dirname(...)` 式と、tests/test_booklink_audit.py:9 / `Path(__file__).resolve().parents[1]` 式の混在
- 問題点: 対象11ファイル内だけでも os.path 式（sourcemap、coverage、structure、projection）と Path.resolve 式（audit、workflow、terms、validate、recovery、raw_citations）が混在している。動作は同じでも、新規テスト追加時にどちらを写すか迷い、片方だけの癖（symlink 解決の有無など）が紛れ込む。
- 提案: どちらか一方（resolve 式）に統一する。conftest 的な共通化が unittest 前提では難しいなら、流儀の統一だけでも価値がある。

### D-3. workflow テストが内部のパス回数を期待値にしている
- 対象: tests/test_translation_workflow.py:127-129 / `compare_catalogs.call_count == 4`、`compare_structure.call_count == 2`、`render_calls == 1`
- 問題点: 「検証が2パス構成で、各章ごとに比較が走る」という実装内部の段取りが期待値化されている。ワークフローの段取りを変える正当なリファクタリング（パスの統合など）で、振る舞いが同じでもテストが落ちる。守りたいのは「失敗時に何もインストールされない」「成功時に全章が揃う」という結果のはず。
- 提案: 呼び出し回数の固定は render の1回だけに留め、比較系は「呼ばれた」ことと最終状態で見る。

### D-4. sourcemap テストが `Marker` を位置引数で組み立てている
- 対象: tests/test_booklink_sourcemap.py:431, 439 / `bsm.Marker(Path("book/lean/Module.lean"), 3, 5, {"target": "proof"}, "instance", None, 6, 9)`
- 問題点: 8個の位置引数が何を意味するか宣言を見ないと読めず、dataclass のフィールド追加・並べ替えでテストが意味を保ったまま壊れる（または壊れずに意味がずれる）。
- 提案: キーワード引数で組み立てる。特に None の引数（decl_name 相当）は名前付きにすると意図（匿名 instance の検証）が伝わる。

### D-5. check_notation_index.py のマクロ抽出が正規表現の形状前提で壊れ方が悪い
- 対象: tests/check_notation_index.py:17-21 / `re.search(r"\\DeclareRobustCommand\{\\BookNotationIndex\}\[1\]\{%.*?\n\}", macros, re.DOTALL).group()`
- 問題点: マクロ本体が「行頭の `}` で終わる」前提の非貪欲マッチで、本体に同じ形の行が増えると途中で切れたマクロをテストしてしまう（失敗ではなく誤った対象の合格になりうる）。またマクロが見つからない場合は `AttributeError` で落ち、原因が分かりにくい。同:22 のエントリ文字列も `\BookNotationIndex` のキー形式をテスト側で再記述しており、マクロ側の形式変更とテスト側の追随が分離している。同:45-48 は素の `assert` で、`python -O` で実行されると検証が丸ごと無力化する点も要確認（Makefile 経由の起動では通常有効）。
- 提案: 抽出できなかった場合はマクロ名を含む明示的なエラーにする。抽出は「次の `\DeclareRobustCommand` または EOF まで」など境界を強くする。assert は明示的な例外送出に置き換える。

## 総括

単体レベルの境界ケースの押さえは全体に丁寧で、特に「弱い一致を covered にしない」「skip とアンカーの矛盾をエラーにする」「失敗時に生成物を残さない」は、過去の事故を踏まえた良い回帰テストになっている。主要な改善余地は、(1) CLI 接着層と一部 tools の無防備さ、(2) 本番データ（用語集・参考文献）に結合したテストの切り分け、(3) ハッシュ等の自己参照的な期待値、の3点に集約される。

## 以上、指摘終わり

---

# 付録: バッチ D1

# 文書・プロセスレビュー バッチD1（sunaemon/math-private @ 9d6e65df）

対象: AGENTS.md、.codex / .claude のスキル定義と付随スクリプト、tools/formalization-viewer/README.md、polish-space-ja/l10n/README.md。原稿本文は対象外。照合先として Makefile、ルート README.md、book-filter（Main.hs）、macros.tex、viewer サーバ実装（book-builder.ts / file-watcher.ts）を参照した。

## A. 実装・他文書との不整合・古い記述

### 1. AGENTS.md:52
- 引用: 「The untranslated Japanese-book chapters are symlinks to their English sources」
- 問題点: polish-space-ja/l10n/README.md:23-24 は「All chapters and appendices now have Japanese draft translations maintained in PO catalogs; no chapter falls back to an English-source symlink」と明記しており、AGENTS.md の「Japanese translation pilot」節の前提（未訳章が英語ソースへのシンボリックリンク）が現状と正反対になっている。同じ前提の古い記述が tools/formalization-viewer/README.md:18「the partial Japanese translation」、同 README の「chapters still symlinked to English retain exact highlights」にも残る。AGENTS.md:52 の「Do not present the mixed-language full book as a completed Japanese edition」も、混在言語ではなくなった現状では根拠を失っている（未レビューの下書きである点は l10n/README 側が正しく述べている）。
- 提案: AGENTS.md の pilot 節を「全章 PO 下書き翻訳済み・レビュー状態は translation-status.json で管理」に書き換え、viewer README の該当文も追随させる。Makefile の `PILOT_BOOK_STEMS`（Makefile:208）という命名も含め、"pilot" の位置づけを再定義するか改名する。

### 2. tools/formalization-viewer/README.md:85
- 引用: 「Scroll sync currently applies to the Markdown, Lean, and TeX panes. The PDF pane is displayed alongside them, but page-level PDF sync is a later step」
- 問題点: 同じ README の :33「Both PDFs resolve the same formalization-marker destinations, so scrolling either pane aligns the other」や、skip 節の「Scrolling either PDF through a skipped region selects the owning Markdown file」という記述と同一文書内で矛盾する。PDF 同期は実装済みとして前段で詳述されており、:85 の段落が古い。
- 提案: :85 の段落を削除するか、現行仕様（PDF もマーカー単位で同期する）に合わせて書き換える。

### 3. tools/formalization-viewer/README.md:168
- 引用: 「only Markdown changes start a build, so the build's own TeX/PDF/JSON output never loops」
- 問題点: 実装 server/book-builder.ts:214 は `.md` と `.lean` の両方の変更でビルドを発火させる（serve.ts:66 のコメントも「when its Markdown or Lean」）。AGENTS.md:82 の「on any `<book>/src/**.md` or `<book>/lean/**.lean` change」という記述が実装に一致しており、README 側が古い。「Markdown 変更だけが発火」という説明は、ループ防止の根拠説明としても誤りになる（実際は出力パスの接頭辞で防いでいるはず）。
- 提案: README を実装に合わせ、発火条件を「対象ツリー配下の .md / .lean」と明記する。

### 4. .codex/skills/book-build/SKILL.md:3, 27-30, 38
- 引用: 「Start `make <book-dir>/build/<stem>.pdf` in the background」「Use `--tex-only` only when the user asks to verify ... without starting a PDF build」
- 問題点: スキルの既定動作はリリース PDF のバックグラウンドビルドで、TeX-only は「ユーザーが求めたときだけ」の例外扱い。一方 AGENTS.md:46 は編集時は book-build を TeX-only で使うことを必須とし、:60 はリリース PDF は明示依頼時のみと定める。AGENTS.md:19 が「a skill describes a preview or release build as its default」でも方針が優先すると留保しているが、スキル側が未更新のままで、AGENTS.md を読まない実行経路では恒常的にリリース PDF が走る。
- 提案: スキルの既定を TeX-only（validate_book_build への委譲、現に --tex-only はそうなっている）に反転させ、PDF 開始は明示フラグ必須に改訂する。

### 5. README.md:88
- 引用: 「Use chapter previews for PDF checks.」（Codex Cloud 保存環境の Start skill 指示）
- 問題点: AGENTS.md:19「Do not build chapter-preview PDFs during routine editing ... only when explicitly requested」と正面から衝突する。保存環境で動くエージェントは AGENTS.md と README の両方を読むよう指示されているため、恒常的なプレビュー実行か、指示の無視かのどちらかになる。
- 提案: Start skill の一文を AGENTS.md の方針（TeX チェックと debug validation を使う）に合わせて修正する。

### 6. README.md:142
- 引用: 「Use targets such as `make <book>/build/<stem>-debug.pdf` only for diagnostic PDFs with visible hyperlink borders」
- 問題点: AGENTS.md:64-68 では debug PDF は「コミット後の必須のレンダー済み検証」の成果物と位置づけられており、"only for diagnostic" という説明と食い違う。新規参加者は debug PDF を「普段は作らない診断用」と誤読しやすい。
- 提案: README 側の説明を「post-commit validation に使う、リンク枠付きの検証用 PDF」程度に寄せる。

### 7. AGENTS.md:98
- 引用: 「The PDF build runs `makeindex` when an `.idx` file exists」
- 問題点: 日本語版は Makefile で `polish-space-ja_INDEXER := $(UPMENDEX)`（upmendex）を使っており、AGENTS.md の記述は英語版前提で日本語版の索引ツールを落としている。
- 提案: 「indexer は本ごとに異なり、日本語版は upmendex」と一言添える。

### 8. AGENTS.md:155-175（Term Index Workflow）
- 引用: 同節は `\termdefine` / `\termdefineas` / `\termuse` / `\termuseas` のみを説明し、`\termforward` への言及は :201（Theorem 節）にしかない
- 問題点: フィルタ（tools/book-filter/Main.hs:2598, 2714）は `\termforwardas{...}{...}` も正式にサポートし、両版の book-section-review スキルも使用を前提にしているが、AGENTS.md の用語索引ワークフローには forward 系2マクロの説明がない。マクロの正本ドキュメントとして欠落。
- 提案: Term Index Workflow に `\termforward` / `\termforwardas` の項を追加する。

### 9. AGENTS.md:46
- 引用: 「The `book-build` and `book-section-review` skills live under `.codex/skills/`; Claude Code's section-review skill lives under `.claude/skills/book-section-review/`」
- 問題点: スキルの所在案内がこの3件だけで、`.claude/skills/book-section-mechanical-checks` と `.codex/skills/book-proof-inventory` が AGENTS.md のどこにも登場しない。特に mechanical-checks は .claude 版 section-review の Phase 0+1 の実体であり、AGENTS.md だけを読む参加者・エージェントには存在が見えない。
- 提案: AGENTS.md にスキル一覧（名前・場所・用途）を集約する。

## B..claude /.codex スキルの二重管理とドリフト

### 10. CLAUDE.md と AGENTS.md がバイト同一（各 32,852 bytes）
- 引用: 両ファイルのサイズと内容が完全に一致する
- 問題点: 実リポジトリで CLAUDE.md が AGENTS.md へのシンボリックリンクなら問題ないが、通常ファイルのコピーなら二重管理となり、いずれドリフトする。本スナップショットからは判別できない。
- 提案: リンクか実ファイルかを確認する。実ファイルなら、リンク化するか、生成元を1つにして CI で一致を検査する。

### 11. book-section-review の二重定義が全面ドリフト
- 引用:.codex 版:12「Use `xhigh` reasoning for this review workflow」／.claude 版「Phase 0 (locate inputs) and Phase 1 (mechanical checks)... dispatch both to a subagent」「do not run book builds (no `make` targets)」
- 問題点: 同名スキルが2ツリーにあり、手順が大きく異なる。.codex 版は抽出スクリプト＋本体での Lean 型検査を中核とし、skip hygiene や coverage の概念がない。.claude 版は Sonnet サブエージェントへの委譲、skip hygiene、coverage 数値を必須化し、本体には make 実行禁止を課す。モデルルーティング（xhigh 本体 vs Sonnet 委譲）も、Lean 証拠の取り方も揃っていない。どちらの手順が現行か、文書のどこにも書かれていない。
- 提案: チェックリストと出力形式は正本を1つにし、ツリー間の差分はモデルルーティングと呼び出し形式だけに限定する。少なくとも「どちらが現行か」を AGENTS.md:46 の案内に明記する。

### 12..claude/skills/book-section-mechanical-checks/SKILL.md:25
- 引用: 「python3.codex/skills/book-section-review/scripts/extract_book_section.py "sec:label-or-title"」
- 問題点:.claude 側のスキルが.codex 側ツリーのスクリプトに依存している。.codex ツリーの整理・改名で.claude 側が静かに壊れる隠れた結合で、AGENTS.md にもこの依存は書かれていない。
- 提案: スクリプトを `tools/` 配下の共有場所へ移すか、両スキルが参照する正本パスを AGENTS.md に明記する。

### 13..codex/skills/book-section-review/SKILL.md:63
- 引用: 「/opt/homebrew/bin/mise exec -- lake env lean polish-space/lean/PolishSpaceBook/PolishSpaces.lean」
- 問題点: macOS Homebrew の絶対パスを lake 不在時のフォールバックとして提示しているが、ルート README が説明する Debian/Codex 環境や Linux では存在しない。AGENTS.md:44「Do not prefix build commands with a custom `PATH`」の精神ともずれる。また.claude 版 mechanical-checks:50-55 は「`polish-space/` から実行しないと `unknown module prefix 'Mathlib'` になる」と警告しているが、.codex 版の手順はリポジトリルートからファイルパス指定で実行する形で、この論点に触れていない（ルート実行で同等に解決できるかは未検証。要確認）。
- 提案: フォールバックを `mise exec --`（PATH 前提）に統一し、実行ディレクトリの注意も mechanical-checks 側と揃える。

### 14..claude/skills/book-section-mechanical-checks/SKILL.md:42, 63
- 引用: 「the system `python3` is too old for the tools」「Bare `python3` (system 3.9) crashes on `Path | str` syntax」
- 問題点: システム Python 3.9 という macOS 前提の事情を普遍的事実として書いている。Debian 環境の Python は 3.12+（README.md の Codex 節）で、この警告はそのままでは誤りになる。
- 提案: 「macOS のシステム Python では」などホストを限定するか、`mise exec --` を使う理由をバージョン非依存の形（ピン留めされたインタプリタを使うため）に書き換える。

### 15. モデル名 `gpt-6-luna` への依存が4文書に分散
- 引用: AGENTS.md:35「delegate the scoped work to `gpt-6-luna` with low reasoning」、.codex/skills/book-maintenance/SKILL.md:3, 15, 18、.codex/skills/book-proof-inventory/SKILL.md の委譲指定
- 問題点: モデル名の実在・利用可否は本レビューでは確認できない。名前が変わる／提供が終わると、AGENTS.md と2スキル（＋openai.yaml 経由の導線）が同時に陳腐化する。book-maintenance が利用不可時の扱い（todo.md に残して報告）を定めている点は良いが、book-proof-inventory には同種のフォールバック記述がない。
- 提案: モデルルーティングは AGENTS.md の1箇所に寄せ、スキル側は「AGENTS.md のルーティングに従う」と参照だけにする。book-proof-inventory にも利用不可時の扱いを足す。

## C. 付随 Python スクリプトの正しさと安全性

### 16..codex/skills/book-build/scripts/build_book_document.py:183-201（wait_for_existing）
- 引用: 「while lock_dir.exists():... time.sleep(2)」
- 問題点: 前任ビルドへの待機ループに全体のタイムアウトも進捗出力もない。記録された pid が（pid 再利用などで）無関係な生存プロセスを指す場合や、ワーカーがハングした場合、呼び出し側は何の表示もなく無限に待ち続ける。AGENTS.md は長時間ビルドを前提にする運用なのに、この待機だけは観測不能。
- 提案: 待機開始時に pid と開始時刻を表示し、上限（例: 数時間）を超えたらロック内容を提示して終了する。

### 17..codex/skills/book-build/scripts/build_book_document.py:175-181, 215-219（remove_lock / release_lock）
- 引用: 「shutil.rmtree(lock_dir)」（所有者確認なし）
- 問題点: pid ファイル未書き込みのロックは 30 秒猶予（MALFORMED_LOCK_GRACE_SECONDS）で緩和されているが、猶予を過ぎてロックを奪われた元のワーカーは、完了時に release_lock で新しい所有者のロックディレクトリを消してしまう。結果として直列化が崩れ、同一 stem の PDF ビルドが重なる可能性がある（発生確率は低いが、ロックの所有トークンがない設計上の穴）。
- 提案: ロック取得時に pid＋開始時刻等のトークンを記録し、解放・除去の前に自分のトークンか照合する。

### 18..codex/skills/book-build/scripts/build_book_document.py:75-99（extract_diagnostics）
- 引用: マーカー「"Missing ", "Extra "」、および「stripped.startswith(("!", "l."))」
- 問題点: `"Missing "` / `"Extra "` は広すぎて、TeX の本当のエラー以外の通常出力（Pandoc や make の "Missing..." 行など）も診断として拾い、先頭5ブロック表示がノイズで埋まりうる。`l.` 始まりも TeX の文脈行以外に一致しうる。診断抽出の精度が低いと、AGENTS.md が重視する「失敗時の診断を先に読む」運用の信頼性が落ちる。
- 提案: マーカーを `"Missing $"`、`"Extra \\"` のような TeX 固有の形に絞り、`l.` は後続が数字の場合だけに限定する。

### 19..codex/skills/book-build/scripts/build_book_document.py:11（DEFAULT_SOURCE）
- 引用: 「DEFAULT_SOURCE = Path("polish-space/src/polish-space-book.md")」
- 問題点: 既定ソースが私家版の全書に固定されており、公開エクスポート（polish-space-ch1 のみ）では既定実行が即エラーになる。AGENTS.md:44 は「the most comprehensive book the current checkout provides」をビルドせよとチェックアウト依存の指示をしているのに、ヘルパーの既定はそれに従わない。SKILL.md にも私家版前提の明記がない。
- 提案: `make list-books` 相当の manifest 発見で既定を選ぶか、少なくとも SKILL.md と --help に「既定は私家版の全書」と明記する。

### 20..codex/skills/book-section-review/scripts/extract_book_section.py:14, 21-38（parse_headers のフェンス処理）
- 引用: 「marker = fence_match.group(2)」「elif marker.startswith(fence * 3)」
- 問題点: フェンスの長さを保持せず開始文字だけを覚えるため、4つ以上の backtick で開いたフェンスの中の ``` 行で誤って閉じる。インデント型コードブロックや複数行 HTML コメント内の `#` 行も見出しとして拾う。本文書では `{=latex}` フェンスや formalization コメントが多用されるため、見出し風の行を含む生 TeX を囲んだ箇所で節範囲がずれる可能性がある。実データで発生するかは未確認。
- 提案: 開いたフェンスの長さを保持し、同長以上のフェンスでのみ閉じる。可能なら Pandoc 自体の見出し一覧と突き合わせる検証を足す。

### 21..codex/skills/book-section-review/scripts/extract_book_section.py:10（HEADER_RE）
- 引用: 「(?:\s+\{(?P<attrs>[^}]*)\})?\s*$」
- 問題点: 行末の `{...}` を無条件に属性として切り取るため、タイトル末尾が数式の波括弧で終わる見出し（例: `$\{0,1\}$` を含む見出し）ではタイトルの切り分けを誤り、attrs 中の `#` をラベルとして拾う可能性がある。
- 提案: 属性として受理する形を `{#...}` / `{.class}` 等の Pandoc 属性文法に限定する。

## D. 冗長・重複と、新規参加者が困る点

### 22. AGENTS.md:64 と:68（コミット後検証の二重規定）
- 引用::64「Use `make validate-debug BOOKS="..."` for the post-commit debug build」／:68「build the affected book's debug PDF instead with `make <book-dir>/build/<stem>-debug.pdf`」
- 問題点: コミット後の手順が2箇所で別のコマンドを正としており、"instead" が何の代わりなのか（validate-debug の代わりか、TeX-only の代わりか）判然としない。validate-debug が同じビルド＋警告検査＋report.json を担うなら、直接ターゲット指定はその内部実装であって独立の手順ではないはず。新規参加者（と別エージェント）はどちらを実行すべきか決められない。
- 提案: 正規手順を validate-debug 1つに決め、:68 は「validate-debug は対象ブックの debug PDF をこのターゲットで作る」という参照に格下げする（あるいは逆に統一する）。

### 23. AGENTS.md:17, 19, 56, 60（同ポリシーの反復）
- 引用: プレビュー／リリース PDF を通常検証で作るな、という同趣旨の禁止が Persistent Book Policies と Build Workflow の少なくとも4箇所にほぼ同文で繰り返される
- 問題点: ポリシー変更時に全箇所の追随が必要で、現に book-build スキル側は追随できていない（指摘4）。重複がドリフトの温床になっている実例。
- 提案: 禁止事項は Persistent Book Policies に集約し、Build Workflow 側は「方針は上記ポリシー参照」と参照のみにする。

### 24. tools/formalization-viewer/README.md:117, 119, 157, 174
- 引用: ブラウザモジュールを「`event-stream.js`」「`lean-lsp.js`」「`file-watch.js`」「`build-status.js`」と.js 名で参照する
- 問題点: リポジトリ内の実ソースは `src/*.ts` で、.js は `build/` へ transpile された生成物（同 README の Type checking 節自身がそう説明している）。本文中の.js 参照は実在ファイルとして検索できず、新規参加者が対応するソースを探せない。生成物の名前で説明するなら、その旨を初出で断るべき。
- 提案: 参照を `src/build-status.ts`（生成物は build/build-status.js）のような併記に統一する。

### 25. tools/formalization-viewer/README.md:170
- 引用: 「it renders just that chapter via `\includeonly` (a few pages, ~1s) instead of the whole 400-page debug PDF」
- 問題点: 全書は第I部だけでも A5 で約200-250ページと見積もられる規模であり、全書の debug PDF が 400 ページというのは古い数字の疑いが強い（ビューアが polish-space-ch1 だけだった頃の名残か）。ページ数は読者の規模感を左右する。
- 提案: 実測ページ数に更新するか、「whole-book debug PDF」とだけ書いて数字を外す。

## 以上、指摘終わり

---

# 付録: バッチ X1

# バッチ X1: TeX/Pandoc テンプレート層レビュー

対象: sunaemon/math-private @ 9d6e65df

- polish-space/tex/macros.tex（1,288 行。polish-space-ja/tex/macros.tex は symlink で同一ファイル）
- polish-space-ja/tex/locale.tex
- tools/pandoc/templates/font-settings.latex
- tools/prepare_pandoc_templates.py
- polish-space/tex/ams-numeric.csl（JA 側は symlink）

確認方法: 全文通読、マクロ定義の機械照合（定義 454 件）、フィルタ側の発行形式（tools/book-filter/Main.hs、DependencyGraph.hs）との照合、英語原稿スナップショット（4082ce17 時点）での使用状況の検索。

---

### X1-1（性能・中）polish-space/tex/macros.tex:5-7

引用:

```tex
\usepackage{tikz}
\usetikzlibrary{graphs,graphdrawing,fit,backgrounds}
\usegdlibrary{force}
```

問題点: `graphs`、`graphdrawing`、`fit` と graphdrawing 用 Lua ライブラリ `force` が、リリース・デバッグ・プレビューを含む全 LuaLaTeX パスで読み込まれる。しかし依存グラフはレイアウト計算を Haskell 側（DependencyGraph.hs）で済ませ、TeX 側へは座標固定の素の `tikzpicture`（ノード配置＋`on background layer`）として発行されるため、TeX 側でグラフ描画レイアウトは走らない。フィルタの発行コードと英語原稿全章（4082ce17 時点）を検索した範囲では、`\graph` コマンド、`fit` の使用はいずれも見つからず、実際に使われているのは `backgrounds`（DependencyGraph.hs:437 の `on background layer`）だけだった。graphdrawing は TikZ ライブラリの中でも読み込みコストが大きい部類で、全パス×両書籍で毎回払っている可能性が高い。

提案: `graphs,graphdrawing,fit` と `\usegdlibrary{force}` を外し、`backgrounds` のみにしてビルドが通るか確認する（HEAD の原稿に万一 `\graph` 利用があれば、その時点で loud に失敗するので試行は安全）。要確認: HEAD 時点の原稿・JA 側生成物に `\graph` 利用がないこと。

### X1-2（正しさ・中）polish-space/tex/macros.tex:135-136

引用:

```tex
\newcommand{\SkipStart}[1]{\ifbooklinkhighlight\hypertarget{skip-#1-start}{}\fi}
\newcommand{\SkipEnd}[1]{\ifbooklinkhighlight\hypertarget{skip-#1-end}{}\fi}
```

問題点: 同ファイル 81〜97 行のコメントは、段落開始位置（垂直モード）での素の `\hypertarget` は行き先が約 1 行上にずれるため、booklink 開始アンカーには `\leavevmode` 付きの `\booklinkanchorhere` が必要だと詳述している。ところが `\SkipStart` は素の `\hypertarget` のままで、同じ配慮がない。フィルタは skip 領域の開始オフセット位置に `\SkipStart{key}` を挿入する（Main.hs:2359）ため、領域が段落・リスト等のブロック先頭から始まる場合は開始アンカーが 1 行分上にずれ、ビューアの skip バンド開始位置がずれる。末尾側の `\SkipEnd` は（booklink の `\booklinkanchor` と同じ理由で）水平モード前提が成り立つので、問題は主に `\SkipStart` 側。

提案: `\SkipStart` も `\booklinkanchorhere` 相当（必要なら `\item` の peek 処理含む）に揃える。意図的に簡略化しているなら、その理由をコメントに残す。

### X1-3（正しさ・低）polish-space/tex/macros.tex:29-33

引用:

```tex
\@ifpackageloaded{caption}{%
  \clearcaptionsetup{table}%
  \AddToHook{env/table/begin}{\captionsetup{skip=6pt}}%
  \AddToHook{env/longtable/begin}{\captionsetup{skip=6pt}}%
}{}
```

問題点: caption パッケージが macros.tex の読み込み時点でロード済みであることに依存し、そうでなければ何の警告もなく素通りする。直下の `\patchcmd` ブロック（37〜43 行）が失敗時に `\PackageError` で loud に止めるのと対照的に、こちらは silent。Pandoc テンプレート側のプリアンブル順序や header-includes の位置が将来変わると、「Pandoc 3.12 が未キャプション表に caption skip を設定して caption が警告する」という、このブロックが防ぐはずの問題が無言で復活する。

提案: 第 2 引数を空にせず `\PackageWarning` を出すか、判定を `\AtBeginDocument` に移して順序依存を解消する。

### X1-4（保守性・低）polish-space/tex/macros.tex:103-127、132-134

引用:

```tex
\NewDocumentCommand{\BooklinkStart}{O{}m}
```

問題点: `\BooklinkStart`/`\BooklinkEnd` の必須引数は、フィルタが発行する booklink 名のカンマ区切りリスト（Main.hs の `booklinkCommand`、`\BooklinkStart[entry=N,kind=K]{名前,...}` 形式）だが、マクロ側では一切使われず黙って読み捨てられる。また `kind` キーも `kind .code:n = {}` で解析だけして捨てている。どちらも設計としては妥当（色付けはビューア側の責務、という同ファイルのコメントとも整合する）が、「必須引数はメタデータであり意図的に描画しない」という肝心な点がコメントのどこにも書かれていない。macros.tex だけを読む保守者は、引数が描画されるべきものに見えて混乱する。加えて skip アンカーのコメント（132〜134 行）は「Gated on the same debug flag as the Booklink coloring」と言うが、直前のコメント（103〜109 行）によれば Booklink の色付け自体は既に TeX 側から撤去されており、参照が陳腐化している。

提案: コメントに「必須引数（名前リスト）と kind はメタデータで、TeX 側では意図的に無視する」と一文を足し、skip 側コメントの "Booklink coloring" への言及を現行の実態（debug フラグ）に合わせて直す。

### X1-5（要確認・低）polish-space/tex/macros.tex:159-176

引用:

```tex
\theoremstyle{\BookTheoremStyle}
\newtheorem*{theorem*}{\BookTheoremName}
...
\theoremstyle{definition}
...
\newtheorem*{statement*}{\BookStatementName}
```

問題点: `statement*` は `\theoremstyle{definition}` の後に定義されるため、ロケールフック `\BookTheoremStyle` が効かない。英語版（デフォルト `plain`）では theorem* 等の本文がイタリックになるのに statement* だけ upright になり、「名前付き環境に収まらない命題見出し」という位置づけと視覚的な扱いが食い違う。日本語版は `\BookTheoremStyle` 自体が `definition`（locale.tex:12）なので差は出ない。意図的なら問題ないが、配置の都合でそうなっているだけにも見える。

提案: 意図的かどうかを確認し、意図的ならコメントを残す。そうでなければ `statement*` の定義を plain グループ側（`\theoremstyle{definition}` の前）へ移す。

### X1-6（保守性・中）tools/pandoc/templates/font-settings.latex 全体、tools/prepare_pandoc_templates.py:43-46

引用（font-settings.latex 冒頭）:

```latex
$-- Based on the bundled Pandoc font-settings.latex partial.
$-- Only the conditional around microtype is local; Japanese books opt out.
```

問題点: この partial は Pandoc 同梱版の全面フォークで、ビルド時にデータディレクトリへコピーされると同梱版を丸ごと shadow する。一方 `prepare_pandoc_templates.py` が上流ドリフトを検出するのは common.latex の caption ブロックだけで、font-settings 側には何のガードもない。Pandoc をアップグレードした際、同梱 font-settings の変更（フォントフォールバック処理の修正など）が取り込まれないまま、しかも検出もされない状態が続く。冒頭コメントの「local なのは microtype の条件分岐だけ」という主張自体が、上流更新のたびに無検証で古くなる。

提案: caption ブロックと同じ流儀のガードを font-settings にも付ける（例: ローカル差分が microtype 条件分岐だけであることを、生成時に同梱版との diff で検証する）。難しければ、少なくとも Pandoc のバージョンアップ時に手動確認すべきファイルとして手順に明記する。

### X1-7（正しさ・低）tools/prepare_pandoc_templates.py:31-45

引用:

```python
block = "\\usepackage{caption}\n\\captionsetup[table]{skip=6pt}\n"
if "\\captionsetup[table]" in common:
    if common.count(block) != 1:
        raise ValueError("Review the updated Pandoc table-caption partial")
```

問題点: ガードは caption ブロックが「変更された」場合には効くが、上流が `\captionsetup[table]` 行自体を取り除いた（`\usepackage{caption}` は残した）場合は `if` 自体が不成立になって素通りし、native-captions の分岐ラップが無言で付かなくなる。その場合、日本語版で caption の表設定が再び読み込まれる——このスクリプトが防ごうとしている、まさにその状態——がエラーにならない。ついでに同種の小さな脆さとして、`Path("tools/pandoc/templates")` がカレントディレクトリ依存である点と、`read_text()`/`write_text()` がロケール既定エンコーディング依存である点がある（Makefile 経由の運用では顕在化していない）。

提案: `\usepackage{caption}` が common に残っているのにブロックが見つからない場合もエラーにする。パスはスクリプト位置基準にし、エンコーディングは `encoding="utf-8"` を明示する。

### X1-8（要確認・低）polish-space/tex/macros.tex:178-183、197-200

引用:

```tex
\newcommand{\bSigma}{{\symbf{\Sigma}}}
% pdf-bookmark: bPi = Π
\newcommand{\bPi}{{\symbf{\Pi}}}
\newcommand{\bDelta}{{\symbf{\Delta}}}
```

問題点: メタデータコメントの付与が兄弟マクロで不揃い。`\bPi` には `pdf-bookmark` があるのに `\bSigma`・`\bDelta` にはなく、lightface 側も `\lPi` にはあるが `\lSigma` にはない。`notation-index` も `\Fsigma`/`\Gdelta` には明示があるのに `\symbf` 系にはない。フィルタがマクロ本体から表示文字列を正しく推論できるなら実害はないが、`\bSigma` のような見出しで頻出する記号ほど、ブックマーク文字列と記号索引の表示が推論頼みになっている。

提案: `\bSigma` を見出しに使った場合の PDF ブックマークと記号索引の表示を一度確認し、推論が外れるようなら他と同様に明示コメントを揃える。要確認。

### X1-9（保守性・微）polish-space/tex/macros.tex:556-557

引用:

```tex
% notation-index: $\CylinderBallRadius{k}$
\newcommand{\CylinderBallRadius}[1]{\rho_{#1}}
```

問題点: 未使用マクロ。英語原稿全章（4082ce17 時点）に使用例がなく、mathmeta の `\notationtype`/`\define` による名前参照もなく、macros.tex 内からも参照されていない（同様の検索で `\SubstTerm`/`\SubstPCA` はレジストリ経由の使用が確認できたが、本マクロにはそれもない）。定義だけが残り、`notation-index` コメントもあるため、将来の保守者が「使われている記号」と誤認しやすい。

提案: 削除するか、実際に ρ_k を使う箇所があればそちらをこのマクロに寄せる。要確認: HEAD 時点の原稿でも未使用であること。

### X1-10（保守性・低）polish-space/tex/ams-numeric.csl:11、138

引用:

```xml
<id>https://github.com/sunaemon/math-private/ams-numeric</id>
```

問題点: CSL スタイルの `<id>` が private リポジトリの URL になっている。polish-space/tex/ は公開版（sunaemon/math）にも共有される共有資産なので、この ID は公開側の成果物にもそのまま載る。CSL の ID は安定した公開識別子であるべきで、到達できない private リポジトリを指すのは不適切だし、将来スタイルを共有・登録する際にも齟齬になる。

提案: 公開側のリポジトリか、リポジトリに依存しない安定した識別子に変える。

併せて要確認（同ファイル 138 行）: 論文誌記事の分岐で誌名に `form="short"` を指定しているため、references.bib 側に短縮誌名のデータがないエントリはフルタイトルにフォールバックする。AMS numeric の体裁（誌名短縮）が揃うかどうかは bib データ側の規約に依存する点として、文献データ側のレビューで確認されたい。

### X1-11（性能・低）tools/pandoc/templates/font-settings.latex:100-109

引用:

```latex
$if(disable-microtype)$
% LuaTeX-ja provides the Japanese typography; do not load incompatible microtype.
$else$
\IfFileExists{microtype.sty}{% use microtype if available
  \usepackage[$for(microtypeoptions)$$microtypeoptions$$sep$,$endfor$]{microtype}
```

問題点: 日本語版は microtype を丸ごと無効化している一方、英語版では全パスで protrusion＋font expansion の効いた microtype が有効。microtype の expansion は LuaLaTeX のパス時間に効くことが知られており、`basicmath` セットは等幅フォントの protrusion を止めるだけで expansion 自体は全フォントに効いたまま。既に `disable-microtype` 変数という受け皿があるので、少なくともドラフト/中間パスで切る選択肢はテンプレート側に用意されていることになる。

提案: パス時間を詰める場合の候補として記録するに留める（最終組版では現行どおり有効でよい）。ビルド側で中間パスに `disable-microtype` を渡すかどうかは Makefile 側の判断事項。

---

## 確認したが問題なかった点

- **EN/JA の tex 共有は複製ではなく symlink**: リポジトリツリー上で polish-space-ja/tex/macros.tex（33 バイト）、ams-numeric.csl（38 バイト）、references.bib（37 バイト）はリンク先パス長であり、実ファイルではない。バイト一致はリンクの帰結で、ドリフトの心配はない。JA 固有の実ファイルは locale.tex のみで、定理名 12 個と `\BookTheoremStyle` をすべて定義し、macros.tex 側の `\providecommand` フックと過不足なく対応している。
- **定義の重複なし**: macros.tex のマクロ定義 454 件を機械照合し、同名の再定義はなかった。`notation-index` 等のメタデータコメントと定義の間に空行が挟まる箇所もなく、フィルタの「直前コメント」前提は満たされている。
- **`\notationindexpage` / `\termindexpage` は現行インターフェース**: フィルタが `\index` の encap として発行する（Main.hs:2822、2844、3170）ため、原稿側に使用例が見えなくても死んだマクロではない。
- **`\qPolAdmCat` は意図的な legacy 保持**: 「incremental builds can read older index files」とコメント明記があり、放置された死コードではない。
- **依存グラフのレイアウトは Haskell 側で計算済み**: TeX 側は座標固定で描くだけ（X1-1 の根拠）。

## 以上、指摘終わり
