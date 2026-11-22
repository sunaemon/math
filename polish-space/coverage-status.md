# Lean対応の事前監査

現行ソースのスナップショット。未リンクを未証明とみなさず、証明追加前の照合に使う。
主張には定義も含む。証明段落は proof 環境内、通常本文はその外の非構造段落で、いずれも全件を集計する。

## 判定反映後の区分

正当な除外対象は、未リンク部分を引用・背景説明・読書案内と確認した段落と、除外指定を妥当と確認した段落の合計。
対象内対応は、本文の skip 指定を除いた対象範囲にリンクが揃う段落。段落全体を形式化したという意味ではない。
skip 指定のない部分対応段落は、残る未リンク部分がすべて対象外と確認された場合に正当な除外対象へ入れる。
未確認・失効した判定は未判定、対象に戻すと判定した箇所は要対応とする。見出し等は構造要素として分ける。
各区分は重複せず、合計は下のリンク集計の総数に一致する。

| 種類      | 対象内対応 | 正当な除外対象 | 要対応 | 保留 | 未判定 | 構造要素 |
| --------- | ---------: | -------------: | -----: | ---: | -----: | -------: |
| statement |        913 |             24 |      0 |    0 |      0 |        0 |
| proof     |       1946 |             20 |      0 |    0 |      0 |        0 |
| prose     |       1240 |            715 |      0 |    0 |      0 |        6 |

## 現行指定によるリンク集計

下表は本文の現行の対象外指定による集計。対象外指定の妥当性は後述の監査で区別する。リンクがあること自体は証明内容の精読完了を意味しない。

| 現行指定によるリンク集計 | 対象内対応 | 部分対応 | 未対応 | 除外指定あり |
| ------------------------ | ---------: | -------: | -----: | -----------: |
| statement                |        913 |        0 |      0 |           24 |
| proof                    |       1946 |        0 |      0 |           20 |
| prose                    |       1240 |        0 |      0 |          721 |

## 作業対象の対応率

外部引用・背景として確認した未リンク部分と、Todoに根拠を残したAstra移譲分を作業分母から分離する。
Astra移譲は未解決であり、対応済みには加算しない。除外指定の未判定・対象に戻す箇所は残りに含める。

| 種類      | 対応済み | 残り | 外部・背景 | Astra移譲 | 作業対象の対応率 |
| --------- | -------: | ---: | ---------: | --------: | ---------------: |
| statement |      913 |    0 |          0 |         0 |          100.00% |
| proof     |     1946 |    0 |          0 |         0 |          100.00% |
| prose     |     1240 |    0 |          0 |         0 |          100.00% |

対象外指定の確認状況は下表に示す。[箇所別の判定](coverage-scope-review.md)を参照。
対象に戻す判定には部分的な局所証明・既存結果の再利用も含むため、件数を新規証明の必要数とはみなさない。

| 対象外指定の判定                   | 主張 | 証明段落 | 通常本文 |
| ---------------------------------- | ---: | -------: | -------: |
| 除外維持が妥当                     |   24 |       20 |      715 |
| 対象に戻す部分あり                 |    0 |        0 |        0 |
| 見出し・導入文として段落数から除く |    0 |        0 |        6 |
| 未判定                             |    0 |        0 |        0 |

| 未対応・部分対応の内訳                              | 主張 | 証明段落 | 通常本文 |
| --------------------------------------------------- | ---: | -------: | -------: |
| リンク追加・範囲修正だけで解消と確認                |    0 |        0 |        0 |
| 既存証明と本文の対応修正が必要                      |    0 |        0 |        0 |
| 定義・構成・証明の補完が必要                        |    0 |        0 |        0 |
| 正当な除外対象（引用・背景説明・読書案内）          |    0 |        0 |        0 |
| 難しい証明をAstraへ移譲（未解決・作業分母から分離） |    0 |        0 |        0 |
| 未判定（未証明とは数えない）                        |    0 |        0 |        0 |

## 章別のリンク集計

| 章                                             | 種類      | 完全対応 | 部分対応 | 未対応 | 除外指定あり |
| ---------------------------------------------- | --------- | -------: | -------: | -----: | -----------: |
| preface                                        | prose     |        5 |        0 |      0 |           97 |
| polish-spaces                                  | statement |        9 |        0 |      0 |            1 |
| polish-spaces                                  | proof     |       26 |        0 |      0 |            0 |
| polish-spaces                                  | prose     |       14 |        0 |      0 |           15 |
| cantor-baire-space                             | statement |        9 |        0 |      0 |            0 |
| cantor-baire-space                             | proof     |       24 |        0 |      0 |            0 |
| cantor-baire-space                             | prose     |       24 |        0 |      0 |           16 |
| concrete-cantor-baire-models                   | statement |        5 |        0 |      0 |            0 |
| concrete-cantor-baire-models                   | proof     |       15 |        0 |      0 |            1 |
| concrete-cantor-baire-models                   | prose     |       54 |        0 |      0 |           15 |
| borel-structure                                | statement |        7 |        0 |      0 |            0 |
| borel-structure                                | proof     |       10 |        0 |      0 |            0 |
| borel-structure                                | prose     |       55 |        0 |      0 |           10 |
| baire-class-functions                          | statement |        8 |        0 |      0 |            1 |
| baire-class-functions                          | proof     |        8 |        0 |      0 |            0 |
| baire-class-functions                          | prose     |        3 |        0 |      0 |            8 |
| perfect-sets-standard-borel-coding             | statement |        4 |        0 |      0 |            0 |
| perfect-sets-standard-borel-coding             | proof     |       14 |        0 |      0 |            0 |
| perfect-sets-standard-borel-coding             | prose     |       12 |        0 |      0 |           12 |
| cauchy-names-polish-representations            | statement |        3 |        0 |      0 |            0 |
| cauchy-names-polish-representations            | proof     |        9 |        0 |      0 |            0 |
| cauchy-names-polish-representations            | prose     |       15 |        0 |      0 |           10 |
| polish-embeddings-borel-refinements            | statement |        8 |        0 |      0 |            0 |
| polish-embeddings-borel-refinements            | proof     |       21 |        0 |      0 |            0 |
| polish-embeddings-borel-refinements            | prose     |        2 |        0 |      0 |           14 |
| analytic-sets-suslin-schemes                   | statement |        7 |        0 |      0 |            0 |
| analytic-sets-suslin-schemes                   | proof     |       20 |        0 |      0 |            0 |
| analytic-sets-suslin-schemes                   | prose     |       11 |        0 |      0 |           10 |
| separation-uniformization-lusin-souslin        | statement |        5 |        0 |      0 |            1 |
| separation-uniformization-lusin-souslin        | proof     |       33 |        0 |      0 |            1 |
| separation-uniformization-lusin-souslin        | prose     |        9 |        0 |      0 |           24 |
| standard-borel-classification-closed-sets      | statement |        4 |        0 |      0 |            0 |
| standard-borel-classification-closed-sets      | proof     |       17 |        0 |      0 |            0 |
| standard-borel-classification-closed-sets      | prose     |        9 |        0 |      0 |            6 |
| borel-measures-polish-spaces                   | statement |       20 |        0 |      0 |            3 |
| borel-measures-polish-spaces                   | proof     |       71 |        0 |      0 |            0 |
| borel-measures-polish-spaces                   | prose     |       22 |        0 |      0 |           16 |
| determinacy                                    | statement |       31 |        0 |      0 |            5 |
| determinacy                                    | proof     |       83 |        0 |      0 |           11 |
| determinacy                                    | prose     |       29 |        0 |      0 |           32 |
| wadge-hierarchy                                | statement |       13 |        0 |      0 |            0 |
| wadge-hierarchy                                | proof     |       40 |        0 |      0 |            0 |
| wadge-hierarchy                                | prose     |       14 |        0 |      0 |           17 |
| polish-groups                                  | statement |       16 |        0 |      0 |            4 |
| polish-groups                                  | proof     |       59 |        0 |      0 |            4 |
| polish-groups                                  | prose     |       28 |        0 |      0 |           45 |
| borel-reducibility-synthesis                   | statement |        5 |        0 |      0 |            1 |
| borel-reducibility-synthesis                   | proof     |        6 |        0 |      0 |            0 |
| borel-reducibility-synthesis                   | prose     |       24 |        0 |      0 |           32 |
| forcing-polish-spaces                          | statement |       34 |        0 |      0 |            1 |
| forcing-polish-spaces                          | proof     |       45 |        0 |      0 |            3 |
| forcing-polish-spaces                          | prose     |       47 |        0 |      0 |           31 |
| effective-dst-lightface-hierarchies            | statement |       43 |        0 |      0 |            0 |
| effective-dst-lightface-hierarchies            | proof     |       73 |        0 |      0 |            0 |
| effective-dst-lightface-hierarchies            | prose     |       48 |        0 |      0 |           26 |
| effective-dst-ranks-effective-refinements      | statement |       54 |        0 |      0 |            1 |
| effective-dst-ranks-effective-refinements      | proof     |       95 |        0 |      0 |            0 |
| effective-dst-ranks-effective-refinements      | prose     |       40 |        0 |      0 |           21 |
| effective-dst-gandy-harrington-dichotomies     | statement |       19 |        0 |      0 |            0 |
| effective-dst-gandy-harrington-dichotomies     | proof     |       53 |        0 |      0 |            0 |
| effective-dst-gandy-harrington-dichotomies     | prose     |       18 |        0 |      0 |           12 |
| computable-polish-spaces-tte                   | statement |       33 |        0 |      0 |            1 |
| computable-polish-spaces-tte                   | proof     |       98 |        0 |      0 |            0 |
| computable-polish-spaces-tte                   | prose     |       50 |        0 |      0 |           12 |
| computable-analysis                            | statement |       30 |        0 |      0 |            0 |
| computable-analysis                            | proof     |       90 |        0 |      0 |            0 |
| computable-analysis                            | prose     |        8 |        0 |      0 |            7 |
| algorithmic-randomness                         | statement |       14 |        0 |      0 |            0 |
| algorithmic-randomness                         | proof     |       29 |        0 |      0 |            0 |
| algorithmic-randomness                         | prose     |        5 |        0 |      0 |            5 |
| weihrauch-reducibility                         | statement |        2 |        0 |      0 |            0 |
| weihrauch-reducibility                         | proof     |        7 |        0 |      0 |            0 |
| weihrauch-reducibility                         | prose     |        6 |        0 |      0 |            7 |
| domain-theory-quasi-polish-spaces              | statement |       12 |        0 |      0 |            2 |
| domain-theory-quasi-polish-spaces              | proof     |       21 |        0 |      0 |            0 |
| domain-theory-quasi-polish-spaces              | prose     |       26 |        0 |      0 |           18 |
| tripos-topos-forcing-realizability             | statement |       18 |        0 |      0 |            0 |
| tripos-topos-forcing-realizability             | proof     |       75 |        0 |      0 |            0 |
| tripos-topos-forcing-realizability             | prose     |       24 |        0 |      0 |           20 |
| inside-effective-topos                         | statement |       22 |        0 |      0 |            3 |
| inside-effective-topos                         | proof     |       39 |        0 |      0 |            0 |
| inside-effective-topos                         | prose     |       18 |        0 |      0 |           19 |
| outlook                                        | prose     |        0 |        0 |      0 |           25 |
| appendix-metric-spaces                         | statement |       12 |        0 |      0 |            0 |
| appendix-metric-spaces                         | proof     |       16 |        0 |      0 |            0 |
| appendix-metric-spaces                         | prose     |        6 |        0 |      0 |           10 |
| appendix-logic                                 | statement |       54 |        0 |      0 |            0 |
| appendix-logic                                 | proof     |      140 |        0 |      0 |            0 |
| appendix-logic                                 | prose     |       72 |        0 |      0 |           12 |
| appendix-set-theory                            | statement |        8 |        0 |      0 |            0 |
| appendix-set-theory                            | proof     |       32 |        0 |      0 |            0 |
| appendix-set-theory                            | prose     |       57 |        0 |      0 |           10 |
| appendix-internal-models                       | statement |       28 |        0 |      0 |            0 |
| appendix-internal-models                       | proof     |       57 |        0 |      0 |            0 |
| appendix-internal-models                       | prose     |       23 |        0 |      0 |            5 |
| appendix-forcing                               | statement |       28 |        0 |      0 |            0 |
| appendix-forcing                               | proof     |       85 |        0 |      0 |            0 |
| appendix-forcing                               | prose     |       38 |        0 |      0 |           11 |
| appendix-borel-absoluteness                    | statement |       55 |        0 |      0 |            0 |
| appendix-borel-absoluteness                    | proof     |       64 |        0 |      0 |            0 |
| appendix-borel-absoluteness                    | prose     |       32 |        0 |      0 |           11 |
| appendix-measure-absoluteness                  | statement |       54 |        0 |      0 |            0 |
| appendix-measure-absoluteness                  | proof     |       67 |        0 |      0 |            0 |
| appendix-measure-absoluteness                  | prose     |       42 |        0 |      0 |           17 |
| appendix-random-forcing                        | statement |       41 |        0 |      0 |            0 |
| appendix-random-forcing                        | proof     |       61 |        0 |      0 |            0 |
| appendix-random-forcing                        | prose     |       18 |        0 |      0 |           16 |
| appendix-lambda-calculus-computability         | statement |       65 |        0 |      0 |            0 |
| appendix-lambda-calculus-computability         | proof     |      114 |        0 |      0 |            0 |
| appendix-lambda-calculus-computability         | prose     |       82 |        0 |      0 |           11 |
| appendix-type-two-computation                  | statement |       48 |        0 |      0 |            0 |
| appendix-type-two-computation                  | proof     |       69 |        0 |      0 |            0 |
| appendix-type-two-computation                  | prose     |       54 |        0 |      0 |            6 |
| appendix-effective-computational-constructions | statement |       64 |        0 |      0 |            0 |
| appendix-effective-computational-constructions | proof     |       93 |        0 |      0 |            0 |
| appendix-effective-computational-constructions | prose     |      141 |        0 |      0 |            4 |
| appendix-category-theory-realizability         | statement |       21 |        0 |      0 |            0 |
| appendix-category-theory-realizability         | proof     |       67 |        0 |      0 |            0 |
| appendix-category-theory-realizability         | prose     |       55 |        0 |      0 |           26 |

証明段落は target:proof に限らず、厳密一致する既存リンクをすべて集計する。
`link_only` は既存の構成・仮定・結論を確認したもの。新しい証明を書かずにリンクを整備できる。
`unreviewed` の近接する主張リンクは探索候補にすぎず、対応済みには加算しない。
未判定 0 件のうち 0 件には直接・近接・手動記録の候補宣言がある。
これは検索の出発点があるという意味で、リンク修正だけで解決すると確認した件数ではない。
補完には既存補題を接続する短い証明や一般形の定義も含む。新しい定理の数や作業量を表す件数ではない。

未解決または弱一致の statement リンク: 0 件。
抜粋指定は、その抜粋を含む主張が一意に定まる場合だけリンクする。

## 章別の内訳

| 章  | 種類 | リンクのみ | 対応修正 | 補完 | 正当な除外対象 | Astra移譲 | 未判定 |
| --- | ---- | ---------: | -------: | ---: | -------------: | --------: | -----: |

## 未対応・部分対応の箇所

## 手動照合の根拠

## 再集計

```sh
python3 tools/booklink_audit.py --out build/coverage-audit
```

全件の位置・本文・候補Lean宣言は同ディレクトリの report.json に保存する。
手動判断は polish-space/coverage-review.json に保持し、本文または根拠ファイルが変われば再確認対象に戻す。
今回の失効した判断: 0 件。
ソース指紋: `ce9e2158bf458f23b90872d2c3e40554d136836415dd843471e0e0b23d9e9158`。

## 追加された主張の証明対応

可算性に関する付録の四つの主張，外部ゲームからの戦略移送，グラフ同型の普遍性の系について，本文の仮定・構成・証明方向を既存の Lean 宣言と照合した。いずれも statement と proof の booklink が既にあり，新たな除外指定や証明の追加は不要だった。

| 本文の主張                                | Lean 宣言                                                      | 照合した内容                                                                                                                                                                    |
| ----------------------------------------- | -------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Separability and second countability      | `PolishSpaceBook.metrizable_separable_iff_second_countable`    | 可分性から可算基，第二可算性から可算稠密集合を得る両方向。Lean は擬距離化可能な空間まで扱う。可算基の構成は mathlib の uniform-space 版を用いる。                               |
| Separability of subspaces                 | `PolishSpaceBook.metrizable_subspace_separable`                | 可算基を部分空間へ制限し，第二可算性から可分性を得る。空の部分空間も含む。                                                                                                      |
| Closed sets and sequences                 | `PolishSpaceBook.first_countable_closed_iff_seq_closed`        | 第一可算性の下で閉包の点を集合内の列の極限として表し，列閉性から閉性を得る。                                                                                                    |
| Sequential criterion for continuity       | `PolishSpaceBook.first_countable_continuous_iff_seqContinuous` | 列連続性から閉集合の逆像の列閉性を示し，直前の閉性判定を適用する。値域に分離公理は不要。                                                                                        |
| Strategy transport from the external game | `PolishSpaceBook.MantheBridge.determined`                      | `toI`・`toII` が有限関数をリストへ移し，`followsI_iff`・`followsII_iff` が整合するプレイの一致を証明する。勝利条件はプレイヤーごとの場合分けで移送する。                        |
| Graph-isomorphism universality corollary  | `PolishSpaceBook.graph_universal_of_external_friedman_stanley` | 分類写像とグラフ符号化を合成する。Friedman–Stanley は `hfs` という明示的な定理仮定であり，外部定理そのものの証明とはしない。元の同値関係が Borel であるという余分な仮定はない。 |

対応するファイルは `lean/PolishSpaceBook/PolishSpaces.lean`，`lean/PolishSpaceBook/BorelDeterminacy.lean`，`lean/PolishSpaceBook/PolishGroupProse.lean`。この三つのモジュールを `make validate-lean` で検証し，エラー・警告がないことを確認した。この照合は上の六件に関するものであり，リンク集計全体の数値を全証明の再査読と読み替えない。
