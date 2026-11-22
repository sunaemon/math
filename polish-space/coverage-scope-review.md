# 形式化対象外の妥当性レビュー

現行の対象外指定に含まれる主張24件・証明段落20件・通常本文721件の確認状況。本文と前後の文脈に照らして判定する。
未判定の通常本文も省略せず列挙する。引用部分と局所的な証明が混在する場合は引用部分だけを除外する。下表は全体が除外された集計単位を数える。

| 判定             | 主張 | 証明段落 | 通常本文 |
| ---------------- | ---: | -------: | -------: |
| 除外維持         |   24 |       20 |      715 |
| 対象に戻す       |    0 |        0 |        0 |
| 段落集計から除く |    0 |        0 |        6 |
| 未判定           |    0 |        0 |        0 |

対象に戻す判定は、本文で証明・構成・使用している局所部分についてのもの。混在する外部入力の再証明までは要求しない。
他章の結果の純粋な再掲と、既存結果から新たな帰結を導く本文証明を区別する。exampleやremarkという環境名だけでは判断しない。
標準的な背景、明示的な引用結果、証明を展開しない紹介は除外を維持する。未形式化であること自体は除外理由にしない。

## 箇所別の判定

### preface

- **除外維持** — `prose` L52–56: 序文の定義可能性の流れを説明し、Borelコード・解析集合・射影階層・相対パラメータという後章の語彙を先取りする。ここで新しい閉包性・構成の証明を提示していない。
- **除外維持** — `prose` L58–61: 序文の定義可能性の流れを説明し、Borelコード・解析集合・射影階層・相対パラメータという後章の語彙を先取りする。ここで新しい閉包性・構成の証明を提示していない。
- **除外維持** — `prose` L74–80: 名前・有限情報・表現の違いを紹介する序文の概説。Cauchy名、二進表示の不連続性、signed-digitとの翻訳の詳細は明示的にCauchy表現章とTTE章へ委ねる。導入中の問いと後章の結論の予告を、その場の新たな構成・計算プログラムとは扱わない。
- **除外維持** — `prose` L82–87: 名前・有限情報・表現の違いを紹介する序文の概説。Cauchy名、二進表示の不連続性、signed-digitとの翻訳の詳細は明示的にCauchy表現章とTTE章へ委ねる。導入中の問いと後章の結論の予告を、その場の新たな構成・計算プログラムとは扱わない。
- **除外維持** — `prose` L89–96: 名前・有限情報・表現の違いを紹介する序文の概説。Cauchy名、二進表示の不連続性、signed-digitとの翻訳の詳細は明示的にCauchy表現章とTTE章へ委ねる。導入中の問いと後章の結論の予告を、その場の新たな構成・計算プログラムとは扱わない。
- **除外維持** — `prose` L98–102: 名前・有限情報・表現の違いを紹介する序文の概説。Cauchy名、二進表示の不連続性、signed-digitとの翻訳の詳細は明示的にCauchy表現章とTTE章へ委ねる。導入中の問いと後章の結論の予告を、その場の新たな構成・計算プログラムとは扱わない。
- **除外維持** — `prose` L104–113: 名前・有限情報・表現の違いを紹介する序文の概説。Cauchy名、二進表示の不連続性、signed-digitとの翻訳の詳細は明示的にCauchy表現章とTTE章へ委ねる。導入中の問いと後章の結論の予告を、その場の新たな構成・計算プログラムとは扱わない。
- **除外維持** — `prose` L115–121: 丸め・関係のselectorを通じて選択問題を動機付け、Part IIへ案内する。Borel uniformizationの新しい局所証明や追加の選択定理を提示せず、必要条件の役割を説明する。
- **除外維持** — `prose` L123–128: Polishの定義とseparability/complete metricの役割を予告する序文の背景。存在と実効的提示を区別する読み方の説明で、新しい構成や計算可能な選択を主張する段落ではない。
- **除外維持** — `prose` L130–133: 五部構成の目的・到達点・前提関係を説明する目次的な案内。個々の結果と証明は参照先の章で独立に監査し、この概要から一括して形式化済みとは扱わない。
- **除外維持** — `prose` L135–140: 五部構成の目的・到達点・前提関係を説明する目次的な案内。個々の結果と証明は参照先の章で独立に監査し、この概要から一括して形式化済みとは扱わない。
- **除外維持** — `prose` L142–147: 五部構成の目的・到達点・前提関係を説明する目次的な案内。個々の結果と証明は参照先の章で独立に監査し、この概要から一括して形式化済みとは扱わない。
- **除外維持** — `prose` L149–154: 各部の内容と参照先を案内する序文であり，新たな局所定理や構成を証明していない。
- **除外維持** — `prose` L156–159: 五部構成の目的・到達点・前提関係を説明する目次的な案内。個々の結果と証明は参照先の章で独立に監査し、この概要から一括して形式化済みとは扱わない。
- **除外維持** — `prose` L167–173: 文献との比較と本書の目的・計算モデル・Leanの役割を説明する編集上の方針。数学的構成や証明を置く箇所ではない。
- **除外維持** — `prose` L175–177: 文献との比較と本書の目的・計算モデル・Leanの役割を説明する編集上の方針。数学的構成や証明を置く箇所ではない。
- **除外維持** — `prose` L179–182: 文献との比較と本書の目的・計算モデル・Leanの役割を説明する編集上の方針。数学的構成や証明を置く箇所ではない。
- **除外維持** — `prose` L184–186: 文献との比較と本書の目的・計算モデル・Leanの役割を説明する編集上の方針。数学的構成や証明を置く箇所ではない。
- **除外維持** — `prose` L194–195: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L197–203: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L205–206: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L208–212: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L214–217: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L219–221: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L223–226: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L231–234: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **段落集計から除く** — `prose` L236–236: 外部入力一覧の小見出しのみであり，数学的主張を含まない。
- **除外維持** — `prose` L238–239: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L241–242: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L244–245: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L247–248: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L250–251: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L253–253: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L255–256: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L258–259: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L261–262: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L264–265: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L267–268: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L270–271: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L273–275: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L277–278: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L280–282: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L284–285: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L287–288: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L290–291: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L293–294: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L296–297: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L299–301: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L303–303: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L305–307: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L309–311: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L313–315: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L317–318: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L320–321: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L323–325: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L327–329: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L331–333: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L335–337: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L339–343: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L345–350: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L352–356: 証明・外部入力・形式化の境界を定める読書規約と外部結果の参照一覧であり，一覧中の結果をここで証明したとは扱わない。
- **除外維持** — `prose` L364–369: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L371–375: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L377–382: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L384–387: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L389–404: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L406–407: 読者の前提知識、付録の役割と利用方法を示す読書案内。列挙した理論の局所的な証明をこの段落には置かない。
- **除外維持** — `prose` L415–420: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L422–426: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L428–433: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L435–441: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L443–448: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L450–455: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **除外維持** — `prose` L457–459: 各目的に応じた読む順序と依存関係を示す読書案内。参照先の定理・証明の監査を省略する指定ではない。
- **段落集計から除く** — `prose` L461–463: 章参照の依存グラフを出力するcenter/DependencyGraphという表示制御だけで、数学的主張を含まない。
- **除外維持** — `prose` L471–472: 全体の用語・記号規約を導入する見出し文で、個別の構成や証明はない。
- **除外維持** — `prose` L474–480: canonical・standard・naturalおよび列・添字族等の記法上の約束を説明する。新しい性質の証明ではない。
- **除外維持** — `prose` L482–483: canonical・standard・naturalおよび列・添字族等の記法上の約束を説明する。新しい性質の証明ではない。
- **除外維持** — `prose` L485–486: countableに有限集合・空集合を含め、countably infiniteと区別する標準的な用語規約。新しい可算性定理の証明ではない。
- **除外維持** — `prose` L488–490: 空間の空の場合と分離公理をどう読むかの全体規約。PolishならHausdorffという標準背景を再述し、新しい局所的証明を置いていない。
- **除外維持** — `prose` L492–493: 近傍、コンパクト、部分・積位相、広義の単調性という標準用語の全体規約。ここでは新しい位相的・順序的な結果の証明を提示しない。
- **除外維持** — `prose` L495–496: 近傍、コンパクト、部分・積位相、広義の単調性という標準用語の全体規約。ここでは新しい位相的・順序的な結果の証明を提示しない。
- **除外維持** — `prose` L498–499: 近傍、コンパクト、部分・積位相、広義の単調性という標準用語の全体規約。ここでは新しい位相的・順序的な結果の証明を提示しない。
- **除外維持** — `prose` L501–502: 近傍、コンパクト、部分・積位相、広義の単調性という標準用語の全体規約。ここでは新しい位相的・順序的な結果の証明を提示しない。
- **除外維持** — `prose` L508–512: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L514–519: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L521–530: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L532–536: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L538–548: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L550–560: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L562–574: canonical・standard・naturalおよび列・添字族等の記法上の約束を説明する。新しい性質の証明ではない。
- **除外維持** — `prose` L576–583: canonical・standard・naturalおよび列・添字族等の記法上の約束を説明する。新しい性質の証明ではない。
- **除外維持** — `prose` L585–598: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L600–613: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **除外維持** — `prose` L615–616: 集合演算、数集合、条件付き制限、距離・閉包・直径、順序数、関係と関数の合成・冪・制限について、標準記法の読み方と意味を固定する。新しい定理や計算の構成を提示せず、後続章・集合論付録の定義を読むための全体規約である。
- **段落集計から除く** — `prose` L618–618: HTMLコメント内の著者・Lean対応表で、読者向け本文には出力されない。新しい数学的主張ではなくソース上の補助情報。
- **段落集計から除く** — `prose` L620–645: HTMLコメント内の著者・Lean対応表で、読者向け本文には出力されない。新しい数学的主張ではなくソース上の補助情報。

### polish-spaces

- **除外維持** — `prose` L3–7: 章の到達点、後続の道具や付録への案内。実際の定義・構成・証明はその位置で別に対象としており、案内文に追加の局所的証明はない。
- **除外維持** — `prose` L9–13: 章の到達点、後続の道具や付録への案内。実際の定義・構成・証明はその位置で別に対象としており、案内文に追加の局所的証明はない。
- **除外維持** — `prose` L17–19: Polishの定義の導入句と、完全距離をデータとして固定しないという定義上の注意。separabilityとcomplete compatible metricの実際の定義は直後の箇条書きおよびLean標準PolishSpaceとの同値で独立に接続済み。
- **除外維持** — `prose` L25–27: Polish空間の定義が特定の距離を指定しないことの説明であり，追加の距離構成を主張していない。
- **除外維持** — `prose` L57–59: 有理数の非Polish性の理由をAlexandrovの定理と有理数・無理数の命題へ明示的に委ねる再掲。ここには別の非例の証明を置いていない。
- **除外維持** — `prose` L68–71: 章の到達点、後続の道具や付録への案内。実際の定義・構成・証明はその位置で別に対象としており、案内文に追加の局所的証明はない。
- **段落集計から除く** — `prose` L75–76: 直後の既存Lean対応を持つ二つの事実へ導く一文のみである。
- **除外維持** — `prose` L90–91: 次の有界距離補題を使う目的の案内であり，補題そのものの証明ではない。
- **除外維持** — `prose` L126–128: 直前のbounded complete compatible metric lemmaの純粋な言い換えで、仮定や結論を強めていない。実際の距離変換・完全性・位相の証明は直前の補題で対象に残る。
- **除外維持** — `prose` L133–137: 後続で証明される閉包操作とその証明方針を要約する導入であり，独立した追加構成ではない。
- **除外維持** — `prose` L154–157: 直後の開部分空間の証明で導入する逆数距離項の動機付けと証明方針の予告。同じ境界回避・完全性の議論は続く証明で対象に残り、この前置きを別の未証明補題とは数えない。
- **除外維持** — `statement` L249–255: 商位相の分離性が崩れうるという一般的注意で、局所的な商の構成・証明は提示しない。Qの例は先の非Polish性の参照に留まる。AGENTS.mdが対象外の例として明示する、証明付きの具体的商を伴わない非閉包性の警告に該当する。
- **除外維持** — `prose` L316–320: Baire category senseと固有名Baire spaceの区別を説明する用語上の注意。既に述べたBaire category theoremの再述で、新しい証明ではない。
- **除外維持** — `prose` L339–341: Alexandrovの定理と有理数・無理数について直前・直後で証明した結果の再掲。新しい仮定変更や別の構成を加えていない。
- **除外維持** — `prose` L426–429: Alexandrovの定理と有理数・無理数について直前・直後で証明した結果の再掲。新しい仮定変更や別の構成を加えていない。
- **除外維持** — `prose` L503–509: 列空間の後章での用途を示す結び。閉部分Baire空間からのCauchy名の全射も表現章へ委ねる予告で、ここで新たな全射を構成しない。

### cantor-baire-space

- **除外維持** — `prose` L10–15: 有限・可算アルファベットの見方、円筒・木の章内容、後章での用途を紹介する章頭の予告。Brouwerの特徴づけ、clopenの有限円筒分解、木の表現の実際の命題・証明は後続箇所で別に対象に残る。
- **除外維持** — `prose` L17–20: 有限・可算アルファベットの見方、円筒・木の章内容、後章での用途を紹介する章頭の予告。Brouwerの特徴づけ、clopenの有限円筒分解、木の表現の実際の命題・証明は後続箇所で別に対象に残る。
- **除外維持** — `prose` L22–23: 有限・可算アルファベットの見方、円筒・木の章内容、後章での用途を紹介する章頭の予告。Brouwerの特徴づけ、clopenの有限円筒分解、木の表現の実際の命題・証明は後続箇所で別に対象に残る。
- **除外維持** — `prose` L25–25: 有限・可算アルファベットの見方、円筒・木の章内容、後章での用途を紹介する章頭の予告。Brouwerの特徴づけ、clopenの有限円筒分解、木の表現の実際の命題・証明は後続箇所で別に対象に残る。
- **除外維持** — `prose` L44–46: 非空語の無限周期反復という記法の読み方を固定し、関数空間の冪と区別するだけの規約。ここで新しい計算可能な反復作用素を証明する箇所ではない。
- **除外維持** — `prose` L54–55: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L149–151: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L155–159: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L187–189: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L201–203: OpenSets、PrefixUpSets、ClosedSetsという既存の標準的な半順序集合の表記を固定するだけで、順序同型やGalois connectionの証明自体は直後に別途対象としている。
- **除外維持** — `prose` L205–207: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L297–298: OpenSets、PrefixUpSets、ClosedSetsという既存の標準的な半順序集合の表記を固定するだけで、順序同型やGalois connectionの証明自体は直後に別途対象としている。
- **除外維持** — `prose` L370–373: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L397–399: Chapter 1で証明したbounded complete compatible metric lemmaを使うという参照のみ。ここで別の距離変換を構成しない。
- **除外維持** — `prose` L439–440: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。
- **除外維持** — `prose` L507–509: 節の目的、直後の定義・命題、前後の特徴づけ、後続の用途への案内。同じ結果の具体的定義・構成・証明は案内先で独立に監査し、ここには追加の局所的証明がない。

### concrete-cantor-baire-models

- **除外維持** — `prose` L5–10: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L15–17: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L98–99: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L126–133: 有限アルファベットのhomeomorphismとBrouwerの特徴づけは前章の明示的な参照で、ここで新たな符号変換の証明を展開しない。
- **除外維持** — `prose` L142–143: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L175–178: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `proof` L192–195: floorとfractional partの標準的な背景定義だけ。後続の連分数の局所証明では既存のInt.floor/Int.fractを使い、その定義をこの段落で新たに証明していない。
- **除外維持** — `prose` L317–318: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L395–397: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L401–404: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L681–683: 既に構成・証明したStern–Brocot、連分数、gap map、特徴関数によるhomeomorphismの再掲・比較。構成の新しい段階や仮定を追加していない。
- **除外維持** — `prose` L687–688: 既出モデル、次の構成の目的や使い道への案内。局所的な新しい式・定理の証明をこの段落には置いていない。続く各モデルの実際の構成と証明は対象に残る。
- **除外維持** — `prose` L750–753: 既に構成・証明したStern–Brocot、連分数、gap map、特徴関数によるhomeomorphismの再掲・比較。構成の新しい段階や仮定を追加していない。
- **除外維持** — `prose` L767–772: 既に構成・証明したStern–Brocot、連分数、gap map、特徴関数によるhomeomorphismの再掲・比較。構成の新しい段階や仮定を追加していない。
- **除外維持** — `prose` L774–778: 各モデルの典型的な用途と比較表への案内で、Diophantine・Gauss map・Ramsey理論などの新しい定理・証明は提示していない。
- **除外維持** — `prose` L782–784: 各モデルの典型的な用途と比較表への案内で、Diophantine・Gauss map・Ramsey理論などの新しい定理・証明は提示していない。

### borel-structure

- **除外維持** — `prose` L4–7: chapter intro / Borel σ-algebra motivation
- **除外維持** — `prose` L9–12: chapter intro / Borel σ-algebra motivation
- **除外維持** — `prose` L14–17: chapter intro / Borel σ-algebra motivation
- **除外維持** — `prose` L57–61: notation-only introduction of the standard first uncountable ordinal omega_1 and the cardinal aleph_1; the cardinality identity is standard set-theoretic background (mathlib Cardinal.ord_aleph), not a claim this chapter proves
- **除外維持** — `prose` L211–217: stabilization-method observation and guide to strictness results
- **除外維持** — `prose` L221–224: roadmap to the universal-set constructions below
- **除外維持** — `prose` L516–520: non-canonicity remark; existence is formalized as exists_decode_eq
- **除外維持** — `prose` L653–657: reading guide for later code-definability results
- **除外維持** — `prose` L665–667: brief guide to later universal-set, boundedness, absoluteness and effective results; these applications are deferred to the linked sections
- **除外維持** — `prose` L669–681: brief guide to later universal-set, boundedness, absoluteness and effective results; these applications are deferred to the linked sections

### baire-class-functions

- **除外維持** — `prose` L3–8: chapter motivation and scope
- **除外維持** — `prose` L10–14: chapter motivation and scope
- **除外維持** — `prose` L33–36: expository explanation of the roles of the two topologies
- **除外維持** — `prose` L77–79: transition to the following formal statement
- **除外維持** — `prose` L132–134: transition to the following formal statement
- **除外維持** — `prose` L146–149: transition to the following formal statement
- **除外維持** — `prose` L184–186: classical real-valued Lebesgue--Hausdorff converse cited to Kechris §24; the reverse implication is not proved in this chapter
- **除外維持** — `statement` L188–192: classical real-valued Lebesgue--Hausdorff converse cited to Kechris §24; the reverse implication is not proved in this chapter
- **除外維持** — `prose` L194–196: classical real-valued Lebesgue--Hausdorff converse cited to Kechris §24; the reverse implication is not proved in this chapter

### perfect-sets-standard-borel-coding

- **除外維持** — `prose` L3–10: 章の二つの目的を予告し、解析集合への拡張と一般のstandard Borel分類は後章へ明示的に委ねる。閉集合のperfect-set定理の実際の構成・証明は後続で対象に残る。
- **除外維持** — `prose` L12–14: 縮小する二分木とstandard Borel codingの位置づけを紹介する動機付け。新しい木の構成やcoding theoremの証明をここでは提示していない。
- **除外維持** — `prose` L16–20: 章の前提と読む順序を示し、一般分類・Effros Borel構造を後章に明示的に委ねる案内。参照先の実際の証明は除外しない。
- **除外維持** — `prose` L33–34: 標準的なperfect-spaceの例と非例の箇条書きへの見出し文だけ。
- **除外維持** — `prose` L36–36: R、閉区間、Cantor空間という標準的なperfect-spaceの例の列挙で、ここでその新しい証明や具体的な構成は提示していない。直後のZの非例など、局所的な議論を持つ項目とは区別する。
- **除外維持** — `prose` L44–45: 次のCantor–Bendixson/perfect-set定理を導入する移行文だけで、数学的な新しい主張・証明を含まない。
- **除外維持** — `prose` L181–183: 直前の二定理から得るcardinality dichotomyへの見出し文。実際のdichotomyとCantor埋め込み・上界を用いる推論は直後で別に対象としている。
- **除外維持** — `prose` L192–200: perfect set propertyの標準的名称を与え、直前の閉集合のdichotomyをZFC/CHと比較して再述する背景説明。解析集合への拡張は後章に委ね、CHの独立性は外部の集合論的背景であり、この段落で新たに証明しない。閉集合の局所的なcardinality argumentは除外しない。
- **除外維持** — `prose` L204–207: 次に掲げる有限Borel階層のstrictness theoremへの予告。一般Polish空間への輸送の実際の証明は直後で対象に残り、この案内には別の推論はない。
- **除外維持** — `prose` L233–235: 位相とBorel構造の違いを動機付け、一般の非可算standard Borel分類を予告する。章頭で明示したとおり、その一般的証明は分類・閉集合空間の章へ委ねる。
- **除外維持** — `prose` L305–307: 直前のCantor–Baire isomorphismの分割片をまとめる表への案内文だけ。分割とBorel性・逆写像の実際の計算は前後で対象に残る。
- **除外維持** — `prose` L350–354: Borel isomorphismが位相やBorel rankを一般には保たないという背景上の注意。新しい反例の局所的な構成・証明をここで展開せず、後続の補題としても用いない。直前の具体的PhiのBorel性の証明は対象に残る。

### cauchy-names-polish-representations

- **除外維持** — `prose` L4–7: chapter motivation, comparison with concrete models, and overview table
- **除外維持** — `prose` L9–12: chapter motivation, comparison with concrete models, and overview table
- **除外維持** — `prose` L14–29: chapter motivation, comparison with concrete models, and overview table
- **除外維持** — `prose` L31–31: chapter motivation, comparison with concrete models, and overview table
- **除外維持** — `prose` L33–40: chapter motivation, comparison with concrete models, and overview table
- **除外維持** — `prose` L106–107: contextual applications and forward pointer to computable analysis
- **除外維持** — `prose` L109–118: contextual applications and forward pointer to computable analysis
- **除外維持** — `prose` L232–236: orientation and reference to the later computational treatment
- **除外維持** — `prose` L283–286: computability preview of the binary-expansion obstruction
- **除外維持** — `prose` L334–337: affine-rescaling observation and qualitative pointer to the effective version

### polish-embeddings-borel-refinements

- **除外維持** — `prose` L3–7: chapter motivation, scope, and reference
- **除外維持** — `prose` L9–14: chapter motivation, scope, and reference
- **除外維持** — `prose` L18–22: background on the Hilbert cube beyond its role in the theorem
- **除外維持** — `prose` L47–52: transition from topological embedding to Borel coding
- **除外維持** — `prose` L56–60: motivation for topology refinement
- **除外維持** — `prose` L62–63: motivation for topology refinement
- **除外維持** — `prose` L153–154: transition to two derived variants
- **除外維持** — `prose` L166–168: transition from refinement to the Baire-space presentation
- **除外維持** — `prose` L208–214: consequences of changing only the compatible Polish topology
- **除外維持** — `prose` L218–223: 直前の位相細分化定理とその系の意味を再述する。新しい帰結の独立した導出を提示していない。
- **除外維持** — `prose` L246–252: the structure preserved by coding
- **除外維持** — `prose` L256–259: 後続の既存定理の用途を示す移行文であり，追加の局所証明ではない。
- **除外維持** — `prose` L263–265: transition to the following Lusin theorem example
- **除外維持** — `prose` L362–368: relation to Polish-group actions

### analytic-sets-suslin-schemes

- **除外維持** — `prose` L3–11: 章の目的、analytic/coanalyticとSuslinの定理の予告、およびMoschovakis/Mansfield–Weitkampへの文献案内。実際の定義とSuslinの定理の局所的な証明は後続で対象に残り、この概要には追加の構成はない。
- **除外維持** — `prose` L135–138: 投影による定義から木で添字付けたSuslin operationへ進む導入。実際の演算の定義と枝による所属条件は直後で別に対象としている。
- **除外維持** — `prose` L166–168: 枝の存在量化と可算Borel演算の違いを説明する概念的比較。非Borelなanalytic集合の存在は前で引用する外部入力であり、この短い解説で新たに非Borel性を証明してはいない。
- **除外維持** — `prose` L192–193: 直後のSuslin-scheme representation theoremへの移行句だけ。実際の正則閉schemeの構成と両方向の証明は直後で対象に残る。
- **除外維持** — `prose` L268–270: 直前のrepresentation theoremを枝と縮小近似の言葉で言い換える純粋な要約。追加の仮定変更や新しいschemeの構成を加えていない。
- **除外維持** — `prose` L272–272: 二つの注意の箇条書きへの見出し文だけ。
- **除外維持** — `prose` L274–277: 閉schemeの像がちょうどanalyticとなるという直前の定理、引用済みの非Borelなanalytic例、およびSuslinの定理を再述した注意。新しい反例や補集合に関する独立の証明をここで提示してはいない。
- **除外維持** — `prose` L279–282: 次章のLusin–Suslinの証明を先取りする比較と参照。有限prefixのBorel testsと縮小近傍の実際の構成・証明は参照先で独立に監査し、この案内から一括して対応済みとは扱わない。
- **除外維持** — `prose` L286–292: 先行するBorel code規約と位相refinementを参照し、次の命題で固定する空間・可算基底・コードの前提を宣言する導入。個々のvalid codeの解釈は先行の再帰に委ね、ここで新たな再帰や有効な選択を構成しない。
- **除外維持** — `prose` L308–311: valid Borel codesのΠ¹₁完全性はKechrisの外部定理として明示的に引用し、この章のcoding/evaluationには不要と本文が区別する。局所的に証明したcoanalyticityや一様評価は除外しない。

### separation-uniformization-lusin-souslin

- **除外維持** — `prose` L3–10: 章の到達点・前提・証明範囲を宣言する案内。Lusin separation、JvN、prefix-separation、Kondoの局所的な構成と証明は対象に残し、引用するscale-existence・closure・norm-comparisonおよび広いregularity理論だけを外部入力として区別する。
- **除外維持** — `prose` L12–16: 章の到達点・前提・証明範囲を宣言する案内。Lusin separation、JvN、prefix-separation、Kondoの局所的な構成と証明は対象に残し、引用するscale-existence・closure・norm-comparisonおよび広いregularity理論だけを外部入力として区別する。
- **除外維持** — `prose` L20–24: 章の到達点・前提・証明範囲を宣言する案内。Lusin separation、JvN、prefix-separation、Kondoの局所的な構成と証明は対象に残し、引用するscale-existence・closure・norm-comparisonおよび広いregularity理論だけを外部入力として区別する。
- **除外維持** — `prose` L122–124: 後の有効版とSilverの証明への参照のみ。ここで再帰的rank boundsを新たに構成する箇所ではない。
- **除外維持** — `prose` L144–146: 直前のJankov–von Neumann定理の適用の読み方を述べるだけで、Borel selectorへの強化や新しい部分選択の構成を加えていない。
- **除外維持** — `prose` L237–239: 直後・直前のLusin–Novikovの可算切片の分解を再述し、Feldman–Mooreへの用途を案内する。分解自体はKechris §18の引用であり、singleton-sectionからBorel部分関数を得る局所的な帰結は証明中で別に対象としている。
- **除外維持** — `statement` L242–252: Lusin–Novikovの可算切片の分解はKechris §18への明示的な外部入力。分解したsingleton-sectionのBorel片から射影・逆写像・第二射影で部分関数を得る後半の局所証明は除外しない。JvNを反復するだけで全点が列挙されるとは扱わない。
- **除外維持** — `proof` L261–267: Lusin–Novikovの可算切片の分解はKechris §18への明示的な外部入力。分解したsingleton-sectionのBorel片から射影・逆写像・第二射影で部分関数を得る後半の局所証明は除外しない。JvNを反復するだけで全点が列挙されるとは扱わない。
- **除外維持** — `prose` L279–283: 直後・直前のLusin–Novikovの可算切片の分解を再述し、Feldman–Mooreへの用途を案内する。分解自体はKechris §18の引用であり、singleton-sectionからBorel部分関数を得る局所的な帰結は証明中で別に対象としている。
- **除外維持** — `prose` L285–288: 直後のLusin–Suslinのprefix-separation証明を予告する要約。同じ一意性と有限prefixのBorel testsは実際の証明で対象に残り、追加の構成をこの前置きには置かない。
- **除外維持** — `prose` L292–296: Lusin–Suslinの位置づけを説明する導入。非Borelなanalytic集合の存在は前章で引用する外部背景であり、単射性によるBorel像の実際の主張と証明は直後で対象に残る。
- **除外維持** — `prose` L298–300: Suslin/Souslinという人名の綴りを統一する編集上の規約だけで、数学的主張ではない。
- **除外維持** — `prose` L315–316: 直後の応用の箇条書きへの導入文だけ。sectionの単射性、Borel range、Borel逆写像の実際の短い推論は除外から戻して接続した。
- **除外維持** — `prose` L465–469: standard Borel分類への第一読の道順と、その後に戻るprojective/scalesの読む順序の案内。参照先の局所的な証明を除外する指定ではない。
- **除外維持** — `prose` L473–475: projective hierarchyの標準的な定義とKechris §37に引用するstrictnessの概説。高階pointclass理論をこの章で構成・証明する箇所ではなく、局所的に使うanalytic/coanalyticの定義・計算は先行部分で別に対象としている。
- **除外維持** — `prose` L477–480: projective hierarchyの標準的な定義とKechris §37に引用するstrictnessの概説。高階pointclass理論をこの章で構成・証明する箇所ではなく、局所的に使うanalytic/coanalyticの定義・計算は先行部分で別に対象としている。
- **除外維持** — `prose` L482–485: projective hierarchyの標準的な定義とKechris §37に引用するstrictnessの概説。高階pointclass理論をこの章で構成・証明する箇所ではなく、局所的に使うanalytic/coanalyticの定義・計算は先行部分で別に対象としている。
- **除外維持** — `prose` L490–494: scaleとcoanalytic normsの一般理論を紹介する外部背景。Kondo証明が使うscale-existence、closure、analytic/coanalytic norm comparisonsは本文が明示的に引用入力とし、Kechris §35/Moschovakis Ch.4へ委ねる。木rankからscaleへの一般構成を局所的に形式化済みとは扱わず、successive minima・存在一意性・graph complexityの局所証明は除外しない。
- **除外維持** — `prose` L496–505: scaleとcoanalytic normsの一般理論を紹介する外部背景。Kondo証明が使うscale-existence、closure、analytic/coanalytic norm comparisonsは本文が明示的に引用入力とし、Kechris §35/Moschovakis Ch.4へ委ねる。木rankからscaleへの一般構成を局所的に形式化済みとは扱わず、successive minima・存在一意性・graph complexityの局所証明は除外しない。
- **除外維持** — `prose` L507–516: scaleとcoanalytic normsの一般理論を紹介する外部背景。Kondo証明が使うscale-existence、closure、analytic/coanalytic norm comparisonsは本文が明示的に引用入力とし、Kechris §35/Moschovakis Ch.4へ委ねる。木rankからscaleへの一般構成を局所的に形式化済みとは扱わず、successive minima・存在一意性・graph complexityの局所証明は除外しない。
- **除外維持** — `prose` L518–521: scaleとcoanalytic normsの一般理論を紹介する外部背景。Kondo証明が使うscale-existence、closure、analytic/coanalytic norm comparisonsは本文が明示的に引用入力とし、Kechris §35/Moschovakis Ch.4へ委ねる。木rankからscaleへの一般構成を局所的に形式化済みとは扱わず、successive minima・存在一意性・graph complexityの局所証明は除外しない。
- **除外維持** — `prose` L575–576: 引用するscale machineryの文献案内と、既に述べたJvN/Kondoの結論を比較する説明。新しい選択関数やgraph complexityの証明を置いていない。
- **除外維持** — `prose` L578–582: 引用するscale machineryの文献案内と、既に述べたJvN/Kondoの結論を比較する説明。新しい選択関数やgraph complexityの証明を置いていない。
- **除外維持** — `prose` L594–596: analytic/coanalytic/projectiveのregularityとSolovayの無矛盾性・独立性結果の文献的概説。Solovay Theorems 1/2、Moschovakis Chs.6–7、determinacy章を参照し、ZFCとZF+DCの違いも明示する。ここで大基数・inner-model・projective-scaleの新規証明を提示せず、局所的な分離・一様化の証明とは区別する。
- **除外維持** — `prose` L598–602: analytic/coanalytic/projectiveのregularityとSolovayの無矛盾性・独立性結果の文献的概説。Solovay Theorems 1/2、Moschovakis Chs.6–7、determinacy章を参照し、ZFCとZF+DCの違いも明示する。ここで大基数・inner-model・projective-scaleの新規証明を提示せず、局所的な分離・一様化の証明とは区別する。
- **除外維持** — `prose` L604–617: analytic/coanalytic/projectiveのregularityとSolovayの無矛盾性・独立性結果の文献的概説。Solovay Theorems 1/2、Moschovakis Chs.6–7、determinacy章を参照し、ZFCとZF+DCの違いも明示する。ここで大基数・inner-model・projective-scaleの新規証明を提示せず、局所的な分離・一様化の証明とは区別する。

### standard-borel-classification-closed-sets

- **除外維持** — `prose` L5–11: 章の前提・読む順序と、直前のBorel Cantor–Bernsteinで使うLusin–Suslinの役割の説明。実際の可算反復・貼り合わせの証明は対象に残り、この案内には別の構成はない。
- **除外維持** — `prose` L65–74: Borel版Cantor–Bernsteinの導入と、先行章のLusin–Suslinをブラックボックスとして使う旨の説明。具体的な構成・証明は直後の定理と証明で別に対応しており、ここで追加の局所的証明を述べていない。
- **除外維持** — `prose` L118–121: 章の前提・読む順序と、直前のBorel Cantor–Bernsteinで使うLusin–Suslinの役割の説明。実際の可算反復・貼り合わせの証明は対象に残り、この案内には別の構成はない。
- **除外維持** — `prose` L292–297: 局所コンパクトなPolish空間のFell位相との標準的比較を外部背景として記録する。直前のEffros標準Borel性の局所証明とは別である。
- **除外維持** — `prose` L299–300: 次の二つの用途を導入する見出し文だけ。閉Baire集合とpruned treesの実際の可測同型は除外から戻して接続した。
- **除外維持** — `prose` L310–320: Kuratowski–Ryll-Nardzewski selection theoremをKechris Theorem 12.13から明示的に引用し、JvNのanalytic-generated measurabilityと比較する文献的背景。この段落でBorel selectorの新しいアルゴリズムや証明を提示してはいない。

### borel-measures-polish-spaces

- **除外維持** — `prose` L10–18: 後続の正則性・弱収束・分解の結果を先取りする章の導入である。
- **除外維持** — `prose` L20–27: 後続の正則性・弱収束・分解の結果を先取りする章の導入である。
- **除外維持** — `prose` L29–37: 章全体の主題・Kechris Ch.17への文献案内。一般位相測度論との定性的比較を含むが、後続で使う正則性・コンパクト性・分解・零一法則の局所的な主張と証明自体は除外しない。
- **除外維持** — `prose` L39–45: 証明範囲の明示。Prokhorov–VaradarajanとPortmanteauは引用する外部入力、conditional expectationと可測因子化は標準測度論の入力であり、その上のBorel条件付き測度の構成・fiber集中・一意性は局所証明として対象に残す。
- **除外維持** — `prose` L49–55: 必要な前提と読む順序を示す案内であり，新しい主張の証明ではない。
- **除外維持** — `prose` L164–169: 確率測度空間の標準定理についてKechrisの番号を示す書誌的な文。局所的な数学の主張・証明ではない。
- **除外維持** — `prose` L171–175: 直前で明示的に引用するProkhorov–Varadarajanの、確率測度空間を再びPolish対象として扱えるという説明的帰結。弱極限の存在を無条件に主張する新しいコンパクト性定理ではなく、局所的な別証明もない。
- **除外維持** — `statement` L178–187: Portmanteau定理はKechris Theorem 17.20から明示的に引用する弱収束の外部基盤。ここでその証明は提示せず、続く局所Prokhorov証明と区別する。
- **除外維持** — `prose` L189–194: 直前のPortmanteau定理のKechris Theorem 17.20への出典表示。本文が明示する引用入力の書誌情報である。
- **除外維持** — `prose` L272–276: 直前に証明したtightnessと相対コンパクト性の同値について、使用方向と他分野への用途を説明する。逆方向でUlamを使う議論自体は直前の証明で対象に残り、この段落で新しいMarkov連鎖・群作用の存在証明を提示しない。
- **除外維持** — `statement` L591–598: 直積測度の条件付き測度を例示する特殊化。核の可測性や積分恒等式の証明はこの例で展開せず、後続の局所補題としても用いない。直後の証明付きconditional distributionsとは区別する。
- **除外維持** — `prose` L640–648: この節で扱う2種類の確率0-1則とBaireカテゴリーの類似を予告する導入。3つの定理と局所証明自体は後続でそれぞれ対応している。
- **除外維持** — `prose` L743–750: 直後のHewitt–Savage定理への導入で、Cesàro極限とE0飽和集合を証明なしに例示する。有限置換不変性を仮定した定理とその局所証明は別に対応済み。
- **除外維持** — `prose` L829–835: 直後に引用するKuratowski–Ulamと位相的0-1則への案内。ここで独立した構成や証明を提示する文ではない。
- **除外維持** — `statement` L838–841: Kuratowski–UlamはKechris Theorem 8.41への明示的な外部引用。続く長方形への帰結と位相的零一法則の局所証明は対象に残し、一般のsection theoremをここで証明済みとは扱わない。
- **除外維持** — `prose` L843–848: Kuratowski–UlamのKechris Theorem 8.41への出典表示。外部入力の文献情報を局所的な証明として数えない。
- **除外維持** — `prose` L923–929: 後章のCohen/random genericityと、この節の零一法則を比較する前方参照。coded meager/null setsの回避とBoolean値・generic評価は参照先の構成で扱い、この段落では新しいgeneric実数やBoolean真理値を構成しない。
- **除外維持** — `prose` L949–952: 直前のMaharam型分類結果を確率代数の例で言い換える。別の分類定理をここで導出していない。
- **除外維持** — `prose` L1253–1259: 章末の分類上の位置付けと既出結論の要約。nonatomic部分と原子質量による分類の局所的な主張・証明は直前の別単位で対象に残す。この段落では新たなパラメータ空間や不変量写像を定義しない。

### determinacy

- **除外維持** — `prose` L5–11: 章の前提・読む順序・証明範囲を明示する案内。Choiceの対角化、Gale–Stewart、Choquetの局所証明、被覆合成・逆極限・帰納、regularity gamesの局所部分は対象に残す。Martinの閉集合unraveling、covering gameでIを排除するlemma、inner-model・大基数理論という外部入力と区別する。
- **除外維持** — `prose` L15–21: 量化子の応答依存を説明するための一回のepsilon–deltaゲームという動機付けの例。連続性の定義を読み換えるだけで、その別証明・実装・後続の補題としての使用はなく、無限ゲームの勝利集合の階層分類とも明示的に区別している。
- **除外維持** — `prose` L176–181: 決定性とregularityの概念的な位置付け、およびMoschovakis Chs.6–7/Kechris §20への案内。後続の各補助ゲーム・payoff closure・strategy transferの局所的証明を除外するものではない。
- **除外維持** — `prose` L183–187: 章の前提・読む順序・証明範囲を明示する案内。Choiceの対角化、Gale–Stewart、Choquetの局所証明、被覆合成・逆極限・帰納、regularity gamesの局所部分は対象に残す。Martinの閉集合unraveling、covering gameでIを排除するlemma、inner-model・大基数理論という外部入力と区別する。
- **除外維持** — `prose` L189–199: 局所証明・引用結果・Mantheからの検証済み輸入を区別する章の証明範囲の説明である。
- **除外維持** — `prose` L314–316: Choquetのmetrization theoremのKechris Theorem 8.18への書誌的参照だけ。直前に展開した局所的な逆方向の証明は対象に残る。
- **除外維持** — `prose` L319–322: 後章のGandy–Harrington topologyでのanalytic witnessの使用を予告する参照。ここでGH topologyや新しいChoquet strategyを構成する箇所ではなく、当該章の局所証明と区別する。
- **除外維持** — `prose` L333–334: Gale–StewartまたはMartinの発表論文への歴史的帰属・引用文だけで、新しい定理の証明ではない。Gale–Stewartの局所的な超限後退帰納は別途対象に残る。
- **除外維持** — `prose` L398–400: Gale–StewartまたはMartinの発表論文への歴史的帰属・引用文だけで、新しい定理の証明ではない。Gale–Stewartの局所的な超限後退帰納は別途対象に残る。
- **除外維持** — `prose` L406–411: Friedman 1971/Martin 1975に引用するZermelo set theory with Choiceでの非証明可能性と、Replacementの役割の概説。制限した決定性の厳密な強さの同値は主張せず、局所的なモデル構成・不完全性の証明も展開しない。
- **除外維持** — `proof` L413–420: Mantheの検証済みMartin証明を参照する証明方針の紹介である。局所的な戦略の定義間の移送は別の補題とLean対応で確認している。
- **除外維持** — `statement` L492–494: Martinの証明全体の案内、またはMartin 1985から明示的に引用する閉集合unravelingの入力。本文で展開する被覆合成・逆極限・超限帰納の局所部分は対象に戻している。
- **除外維持** — `proof` L496–500: Martinの証明全体の案内、またはMartin 1985から明示的に引用する閉集合unravelingの入力。本文で展開する被覆合成・逆極限・超限帰納の局所部分は対象に戻している。
- **除外維持** — `proof` L502–508: 閉集合の制御付き被覆と戦略持ち上げは明示的に輸入される構成の性質として扱う。通常の閉ゲーム決定性だけから局所的に構成したとはしない。
- **除外維持** — `proof` L560–564: 普遍的unravelabilityの定義とsigma代数性はMantheの輸入されたBorel帰納法の記述であり，本書固有の新規証明義務とはしない。
- **除外維持** — `statement` L566–569: 普遍的unravelabilityの定義とsigma代数性はMantheの輸入されたBorel帰納法の記述であり，本書固有の新規証明義務とはしない。
- **除外維持** — `proof` L571–577: 普遍的unravelabilityの定義とsigma代数性はMantheの輸入されたBorel帰納法の記述であり，本書固有の新規証明義務とはしない。
- **除外維持** — `proof` L579–583: 被覆に関する普遍量化，塔の構成，和集合および合成の議論は明示的に参照する輸入済みBorel帰納法の説明である。別に記載された局所被覆補題と混同しない。
- **除外維持** — `proof` L585–592: 被覆に関する普遍量化，塔の構成，和集合および合成の議論は明示的に参照する輸入済みBorel帰納法の説明である。別に記載された局所被覆補題と混同しない。
- **除外維持** — `proof` L594–599: 被覆に関する普遍量化，塔の構成，和集合および合成の議論は明示的に参照する輸入済みBorel帰納法の説明である。別に記載された局所被覆補題と混同しない。
- **除外維持** — `proof` L601–602: 被覆に関する普遍量化，塔の構成，和集合および合成の議論は明示的に参照する輸入済みBorel帰納法の説明である。別に記載された局所被覆補題と混同しない。
- **除外維持** — `proof` L604–607: 被覆に関する普遍量化，塔の構成，和集合および合成の議論は明示的に参照する輸入済みBorel帰納法の説明である。別に記載された局所被覆補題と混同しない。
- **除外維持** — `proof` L609–613: 引用したunraveling証明を全木に適用する結論の再述であり，対応する決定性定理は輸入証明と局所戦略移送によりLeanで確認される。
- **除外維持** — `prose` L615–621: 輸入したLean定理の出典と木の逆極限の表現を説明する来歴情報である。
- **除外維持** — `prose` L639–641: Martinの完全なcovering constructionについての原論文・Kechris §20への文献案内。直前に展開したcovering composition・inverse limits・rank inductionの局所証明とは区別する。
- **除外維持** — `prose` L647–652: Friedman 1971/Martin 1975に引用するZermelo set theory with Choiceでの非証明可能性と、Replacementの役割の概説。制限した決定性の厳密な強さの同値は主張せず、局所的なモデル構成・不完全性の証明も展開しない。
- **除外維持** — `statement` L658–660: 解析的決定性とsharpsの同値はMartin・Harringtonの結果として引用し、inner-model構成は本文に展開していない。
- **除外維持** — `prose` L662–665: Martin/Harringtonのanalytic determinacyと全実数のsharpの同値、およびmeasurable cardinalからの十分条件を引用するinner-model理論の概説。本文がfine-structural sharpの定義・構成を使わないことも明示し、これらの外部定理の証明を局所課題に含めない。
- **除外維持** — `prose` L667–669: Martin/Harringtonのanalytic determinacyと全実数のsharpの同値、およびmeasurable cardinalからの十分条件を引用するinner-model理論の概説。本文がfine-structural sharpの定義・構成を使わないことも明示し、これらの外部定理の証明を局所課題に含めない。
- **除外維持** — `prose` L671–673: PDという引用する背景公理の内容と、後のMartin–Steel theoremへの道案内。ここでprojective gamesの勝利戦略を構成せず、PDを仮定してregularityを得る補助ゲームの局所証明は別途対象に残す。
- **除外維持** — `prose` L675–677: PDという引用する背景公理の内容と、後のMartin–Steel theoremへの道案内。ここでprojective gamesの勝利戦略を構成せず、PDを仮定してregularityを得る補助ゲームの局所証明は別途対象に残す。
- **除外維持** — `prose` L681–686: regularity gamesの役割と証明範囲の導入。Banach–Mazur・payoff coding・strategy transfer・covering estimate・Borel hull・Davisの局所証明は対象に残し、Iを排除する外部game lemmaだけを引用入力として明示している。
- **除外維持** — `prose` L688–692: regularity gamesの役割と証明範囲の導入。Banach–Mazur・payoff coding・strategy transfer・covering estimate・Borel hull・Davisの局所証明は対象に残し、Iを排除する外部game lemmaだけを引用入力として明示している。
- **除外維持** — `prose` L1020–1025: 標準pointclassesの連続逆像閉性と、先行する条件付きregularity theoremへのBorel determinacy/PDの適用を要約する背景。ここで新しいprojective codeの構成や別のBaire-property証明を展開してはいない。局所的なpayoffの連続逆像表示と点クラス閉性を仮定した証明は対象に残す。
- **除外維持** — `prose` L1148–1152: Borel正測度部分集合を持たない場合にcovering gameでIが勝てないというMoschovakis 6A.17の明示的引用。integer presentationへの適用は直前に証明したlegal-history coding/strategy liftingを参照する再述で、その局所的な証明は除外しない。
- **除外維持** — `prose` L1173–1176: Borel/projectiveの標準的な閉性とBorel determinacy/PD/ADの帰結を述べる背景上の適用。局所的な有限測度の輸送とsigma-finite exhaustionの議論はここから分離して実際のBorel embedding・pushforward・completion pullback・可算unionの証明へ接続した。
- **除外維持** — `prose` L1182–1185: open approximationとBorel hullを混同しないための例示的な注意。閉疎・正測度集合の具体的構成や証明をここで提示せず、後続の局所補題にも用いない。本文のmeasurability proofはopen agreementを仮定せず、既に対象であるBorel hullの議論を使う。
- **除外維持** — `prose` L1337–1341: closed perfect-set theoremへの後方参照、引用するanalytic perfect-set theoremとPDの帰結を含む章のregularityの総括。追加のCantor embeddingやanalytic witnessの証明をこの段落で提示せず、直前のDavis gameと局所的なperfect-set reductionは対象に残る。
- **除外維持** — `prose` L1343–1347: closed perfect-set theoremへの後方参照、引用するanalytic perfect-set theoremとPDの帰結を含む章のregularityの総括。追加のCantor embeddingやanalytic witnessの証明をこの段落で提示せず、直前のDavis gameと局所的なperfect-set reductionは対象に残る。
- **除外維持** — `prose` L1357–1359: 次に引用するL(R)-determinacyの大基数定理の定式化への案内だけ。ADの定義と、実際のChoice diagonalizationによる矛盾は除外から戻し、それぞれAxiomOfDeterminacy/not_axiomOfDeterminacyへ接続した。
- **除外維持** — `statement` L1361–1366: L(R)のADとWoodin基数について、直接含意の十分条件と無矛盾性強度を区別した外部の内的モデル理論の紹介。本文はこの大基数定理の証明を展開していないため、対象外指定を維持する。
- **除外維持** — `prose` L1368–1373: ADのregularityの帰結とSolovay modelとの比較という外部の背景。Solovay collapseやinner-model calibrationをここで新たに構成・証明せず、局所ゲームからのregularityの証明と区別する。
- **除外維持** — `prose` L1379–1380: Martin–Steel 1989の大基数からPDへの外部定理、そのfinite-levelの読み方・inner models/iteration/absolutenessによる証明の文献的概説と強さの位置付け。Woodin基数・iteration strategies・projective absolutenessの構成はこの章の局所証明ではなく、別章で使う際の仮定も保持する。
- **除外維持** — `statement` L1382–1384: Martin–Steelの大基数からPDへの定理を引用し、その証明を本文の議論に含めていない。
- **除外維持** — `prose` L1386–1395: Martin–Steel 1989の大基数からPDへの外部定理、そのfinite-levelの読み方・inner models/iteration/absolutenessによる証明の文献的概説と強さの位置付け。Woodin基数・iteration strategies・projective absolutenessの構成はこの章の局所証明ではなく、別章で使う際の仮定も保持する。
- **除外維持** — `prose` L1397–1401: Martin–Steel 1989の大基数からPDへの外部定理、そのfinite-levelの読み方・inner models/iteration/absolutenessによる証明の文献的概説と強さの位置付け。Woodin基数・iteration strategies・projective absolutenessの構成はこの章の局所証明ではなく、別章で使う際の仮定も保持する。
- **除外維持** — `prose` L1403–1410: AD・大きな基数・LSA・Sealingに関する引用結果の概説であり，内部モデル構成をここで証明または局所証明の未明示入力として使用していない。
- **除外維持** — `prose` L1412–1421: AD・大きな基数・LSA・Sealingに関する引用結果の概説であり，内部モデル構成をここで証明または局所証明の未明示入力として使用していない。

### wadge-hierarchy

- **除外維持** — `prose` L3–8: Wadge階層の歴史，章の証明範囲，必要な決定性の位置付けを要約する導入である。
- **除外維持** — `prose` L10–13: Wadge hierarchyの動機・歴史的出典・前提・読む順序と証明範囲の案内。選んだ位相への依存は位相の異なるpresentationとの概念的比較であり、新しい反例の証明を置かない。Wadge lemma・difference hierarchy・Martin–Monkの局所証明と、外部のprojective/AD-level分類を区別する。
- **除外維持** — `prose` L15–19: Wadge hierarchyの動機・歴史的出典・前提・読む順序と証明範囲の案内。選んだ位相への依存は位相の異なるpresentationとの概念的比較であり、新しい反例の証明を置かない。Wadge lemma・difference hierarchy・Martin–Monkの局所証明と、外部のprojective/AD-level分類を区別する。
- **除外維持** — `prose` L23–29: Wadge hierarchyの動機・歴史的出典・前提・読む順序と証明範囲の案内。選んだ位相への依存は位相の異なるpresentationとの概念的比較であり、新しい反例の証明を置かない。Wadge lemma・difference hierarchy・Martin–Monkの局所証明と、外部のprojective/AD-level分類を区別する。
- **除外維持** — `prose` L228–234: 決定性の仮定がない場合のsemi-linearityの失敗、とくにL内のprojective集合についての外部の背景。具体的なincomparable集合を構成・証明する箇所ではなく、補集合と比較できないことだけではsemi-linearityに反しないという読み方を補足する。
- **除外維持** — `prose` L238–241: 直後のtrivial/clopen/open/closed/second-level計算への導入と一覧表の説明。Delta02に単一の完全集合がないという広い階層の位置付けを含むが、この段落に独立した対角化証明はなく、後続の局所補題にも使わない。実際の完全代表元・連続還元・差階層の局所証明は対象に残す。
- **除外維持** — `prose` L243–243: 直後のtrivial/clopen/open/closed/second-level計算への導入と一覧表の説明。Delta02に単一の完全集合がないという広い階層の位置付けを含むが、この段落に独立した対角化証明はなく、後続の局所補題にも使わない。実際の完全代表元・連続還元・差階層の局所証明は対象に残す。
- **除外維持** — `prose` L253–256: 直後の局所的な次数計算と後続の差階層の位置を案内する比較表の説明である。
- **除外維持** — `prose` L498–502: Hausdorffの差階層とそのconverseの定理を予告する橋渡し。first-entry parityによる定義・Delta02への包含・Hausdorffの逆方向の局所証明は直後で対象に残り、この前置きで追加の構成や別証明は提示しない。
- **除外維持** — `prose` L508–517: Hausdorff差分階層の導入と歴史的出典表示。具体的な定義、Delta02への包含、Hausdorffの逆方向の定理・証明は後続で個別に対応済みで、この導入を独立した証明とは数えない。
- **除外維持** — `prose` L565–567: Hausdorffの差階層とそのconverseの定理を予告する橋渡し。first-entry parityによる定義・Delta02への包含・Hausdorffの逆方向の局所証明は直後で対象に残り、この前置きで追加の構成や別証明は提示しない。
- **除外維持** — `prose` L682–685: 任意のuncountable Polish spaceでの差階層のpropernessはKechris §22.Eへの明示的な外部引用。ここでは全countable ordinalにわたる厳密性の構成を展開せず、局所的なHausdorff表示定理とは区別する。
- **除外維持** — `prose` L689–690: 次のBorel Wadge degree全体の分類の導入。局所的なcoarse partial order・Martin–Monk・0始まりのrankは対象に残し、細かいself-dual patternとVeblenによる長さの計算は引用する外部結果として区別する。
- **除外維持** — `prose` L823–829: Steel–Van Wesepの自己双対性と共終性の構造定理、およびKechris §21のVeblen関数による全長の外部分類。本文はその計算を導出しないと明示する。粗い次数の整列順序とstrict initial-segment rankの実際の構成は除外から戻し、difference indexとrankも同一視しない。
- **除外維持** — `prose` L837–843: Steel–Van Wesepの自己双対性と共終性の構造定理、およびKechris §21のVeblen関数による全長の外部分類。本文はその計算を導出しないと明示する。粗い次数の整列順序とstrict initial-segment rankの実際の構成は除外から戻し、difference indexとrankも同一視しない。
- **段落集計から除く** — `prose` L847–848: 後続の用途一覧への導入見出し相当の文である。
- **除外維持** — `prose` L896–899: Kechris §21とMoschovakis Ch.7の完全な扱いへの文献案内だけで、新しい数学の証明ではない。

### polish-groups

- **除外維持** — `prose` L10–13: 章の動機・参考文献・前提・読む順序・証明範囲の案内。logic actions、Vaught transforms、orbit analyticity、Effrosの局所証明は対象に残す。Becker–KechrisのPolish basis構成とHjorthの障害定理を引用入力として区別し、分類理論や作用の新たな符号化をこの導入で証明したとは扱わない。
- **除外維持** — `prose` L15–19: 章の動機・参考文献・前提・読む順序・証明範囲の案内。logic actions、Vaught transforms、orbit analyticity、Effrosの局所証明は対象に残す。Becker–KechrisのPolish basis構成とHjorthの障害定理を引用入力として区別し、分類理論や作用の新たな符号化をこの導入で証明したとは扱わない。
- **除外維持** — `prose` L21–29: 章の動機・参考文献・前提・読む順序・証明範囲の案内。logic actions、Vaught transforms、orbit analyticity、Effrosの局所証明は対象に残す。Becker–KechrisのPolish basis構成とHjorthの障害定理を引用入力として区別し、分類理論や作用の新たな符号化をこの導入で証明したとは扱わない。
- **除外維持** — `prose` L31–37: 局所Vaught変換・論理作用・Lopez--Escobarの証明と外部turbulence定理の役割を分けた章の案内である。
- **除外維持** — `prose` L41–47: 章の動機・参考文献・前提・読む順序・証明範囲の案内。logic actions、Vaught transforms、orbit analyticity、Effrosの局所証明は対象に残す。Becker–KechrisのPolish basis構成とHjorthの障害定理を引用入力として区別し、分類理論や作用の新たな符号化をこの導入で証明したとは扱わない。
- **除外維持** — `prose` L72–76: 群の例の一覧への導入と既存のp-adic notation metadataだけ。具体的なCantor基本開部分群、有限台置換の稠密性、S_inftyのPolish性、Aut(M)の閉部分群は除外から戻して実際の証明へ接続した。
- **除外維持** — `prose` L129–134: 次の局所コンパクト性とnon-Archimedean性を予告する見出し相当の導入。定義や局所証明はこの文の後で別に対応している。
- **除外維持** — `prose` L153–155: 既出例のnon-Archimedean性と局所コンパクト性を比較する説明。Cantor群の有限零座標の基本開部分群は実際の証明に戻した。p-adic体・整数環の局所体の性質はSutherland Lectures 8–9への明示的な引用で、ここで別のvaluation/completionの証明を展開しない。
- **除外維持** — `prose` L276–279: non-Archimedean representationとVaught transformsの用途を説明する橋渡し。一般的なlogic-action codingや新しいinvariant Borel objectをここで構成する箇所ではなく、先行・後続の局所構成や恒等式は対象に残す。
- **除外維持** — `prose` L452–457: Vaught-transformの議論の出典Gao §3.2を示す書誌情報。局所的な数学の主張ではない。
- **除外維持** — `prose` L459–462: Vaught変換の後続用途を列挙する移行文であり，新たな変換の構成や閉包性証明ではない。
- **除外維持** — `statement` L472–476: Becker–Kechrisから引用するPolish基底の存在・性質の区画。続く作用の連続性の局所証明は対象に残している。
- **除外維持** — `proof` L498–504: Becker–Kechrisから引用するPolish基底の存在・性質の区画。続く作用の連続性の局所証明は対象に残している。
- **除外維持** — `proof` L506–511: Becker–Kechrisから引用するPolish基底の存在・性質の区画。続く作用の連続性の局所証明は対象に残している。
- **除外維持** — `proof` L513–516: Becker–Kechrisから引用するPolish基底の存在・性質の区画。続く作用の連続性の局所証明は対象に残している。
- **除外維持** — `proof` L518–522: Becker–Kechrisから引用するPolish基底の存在・性質の区画。続く作用の連続性の局所証明は対象に残している。
- **除外維持** — `prose` L721–726: Lopez–Escobarへの歴史的帰属と原論文の出典表示。定理・局所証明そのものは別に対応済み。
- **除外維持** — `prose` L891–896: 相対化された帰納のGao/Vaughtへの出典表示。帰納の局所的な内容は直前で別に対応している。
- **除外維持** — `prose` L898–905: Lopez–Escobarで証明したinvariant Borel classのdefinabilityの意味を説明し、標準的なScott sentenceの背景を紹介する。Lopez–Escobarの局所帰納は対象に残し、Scott sentenceの一般構成はこの章で展開も後続の局所証明への入力としての使用もしていない。
- **除外維持** — `prose` L913–923: 第一階Vaught予想の定義・cardinality版とperfect-set強化を説明する未解決問題の背景。完全理論の模型族やperfect antichainを構成したとは扱わない。Mod(T)の実際のBorel性と制限同型関係の解析性は後の説明から切り出して、canonical first-order syntaxと実際のmodel codes上で証明へ接続した。
- **除外維持** — `prose` L925–931: 第一階Vaught予想の定義・cardinality版とperfect-set強化を説明する未解決問題の背景。完全理論の模型族やperfect antichainを構成したとは扱わない。Mod(T)の実際のBorel性と制限同型関係の解析性は後の説明から切り出して、canonical first-order syntaxと実際のmodel codes上で証明へ接続した。
- **除外維持** — `prose` L933–937: Silverのcoanalyticな場合と一般logic-space同型のanalytic-completeな場合を比較する、標準分類結果を用いた背景説明。実際のMod(T)のBorel性と制限同型関係の解析性は除外から切り出し、canonical first-order satisfactionの帰納、理論の可算共通部分、Borel制限と実際の同型関係の証明へ接続した。
- **除外維持** — `prose` L944–952: Lopez–Escobarで証明したinvariant Borel classのdefinabilityの意味を説明し、標準的なScott sentenceの背景を紹介する。Lopez–Escobarの局所帰納は対象に残し、Scott sentenceの一般構成はこの章で展開も後続の局所証明への入力としての使用もしていない。
- **除外維持** — `prose` L954–954: 第一階Vaught予想の定義・cardinality版とperfect-set強化を説明する未解決問題の背景。完全理論の模型族やperfect antichainを構成したとは扱わない。Mod(T)の実際のBorel性と制限同型関係の解析性は後の説明から切り出して、canonical first-order syntaxと実際のmodel codes上で証明へ接続した。
- **除外維持** — `prose` L956–963: 第一階Vaught予想の定義・cardinality版とperfect-set強化を説明する未解決問題の背景。完全理論の模型族やperfect antichainを構成したとは扱わない。Mod(T)の実際のBorel性と制限同型関係の解析性は後の説明から切り出して、canonical first-order syntaxと実際のmodel codes上で証明へ接続した。
- **除外維持** — `prose` L965–969: Ackerman–Freer–KnightのOctober 2026 preprintに明示的に引用するinfinitary/topological perfect-set版の反例と、第一階予想との区別を述べる文献的背景。CHによるcardinalityの読み方も反例の位置付けで、ここでその文・モデル・作用を構成する証明は提示しない。
- **除外維持** — `prose` L971–976: Ackerman–Freer–KnightのOctober 2026 preprintに明示的に引用するinfinitary/topological perfect-set版の反例と、第一階予想との区別を述べる文献的背景。CHによるcardinalityの読み方も反例の位置付けで、ここでその文・モデル・作用を構成する証明は提示しない。
- **除外維持** — `prose` L978–982: Ackerman–Freer–KnightのOctober 2026 preprintに明示的に引用するinfinitary/topological perfect-set版の反例と、第一階予想との区別を述べる文献的背景。CHによるcardinalityの読み方も反例の位置付けで、ここでその文・モデル・作用を構成する証明は提示しない。
- **除外維持** — `prose` L999–1003: 閉部分群の作用から可算構造への一般codingはBecker–Kechris Theorem 2.7.3への明示的な外部引用。閉部分群としてのAut(M)とnon-Archimedean representationの局所証明自体は別に対象に残す。
- **除外維持** — `prose` L1009–1018: この節で示すグラフ例の構成と解析性、および後で外部定理として引用するuniversalityを予告する節導入。具体的な符号化・作用・局所証明は後続で個別に接続している。
- **除外維持** — `statement` L1097–1102: Friedman--Stanleyのグラフ符号化定理とgadgetの説明は引用結果である。その入力から普遍性を導く局所的な系は明示仮定付きLean証明に別途対応する。
- **除外維持** — `prose` L1104–1111: Friedman–Stanley/Gaoに引用する一般のgraph-gadget coding定理の構成方針と文献案内。rigid gadgetsの具体的な設計・soundness/completenessの局所証明をこの章では展開せず、既に対象であるグラフ符号空間・relabeling・同型解析性とは区別する。
- **除外維持** — `prose` L1113–1114: Friedman–Stanley/Gaoに引用する一般のgraph-gadget coding定理の構成方針と文献案内。rigid gadgetsの具体的な設計・soundness/completenessの局所証明をこの章では展開せず、既に対象であるグラフ符号空間・relabeling・同型解析性とは区別する。
- **除外維持** — `prose` L1132–1137: 既述のLopez--Escobarとグラフ分類の解釈および後続の分類問題への案内であり，新しい符号化構成ではない。
- **除外維持** — `prose` L1139–1143: 引用するgraph universalityと、局所的に証明したLopez–Escobarの意味をグラフの分類に読み換える用途の説明。新しい構造言語・還元写像・無限論理文をこの段落で構成するものではなく、sourceの実際のgraph action/projection/definabilityの証明は対象に残す。
- **除外維持** — `prose` L1163–1168: 直後のEffros定理の導入文。数学的な仮定・結論・証明は定理本体で別に対応している。
- **除外維持** — `statement` L1184–1186: 閉部分群によるPolish商と商写像の開性はGao Theorem 2.2.10からの引用。これを適用するEffrosの局所証明は別に対象である。
- **除外維持** — `prose` L1188–1193: Polish quotientのGao Theorem 2.2.10への出典表示。明示的に引用する外部インフラの書誌情報である。
- **除外維持** — `prose` L1326–1331: turbulenceの動機と、non-Archimedeanなlogic-action codingとの定性的比較。Hjorthの非分類定理は明示的な外部入力であり、ここでHjorth analysisやabsolutenessを再証明する箇所ではない。local orbitとturbulenceの具体的な定義・前後の局所帰結は対象に残す。
- **除外維持** — `prose` L1333–1338: turbulenceの動機と、non-Archimedeanなlogic-action codingとの定性的比較。Hjorthの非分類定理は明示的な外部入力であり、ここでHjorth analysisやabsolutenessを再証明する箇所ではない。local orbitとturbulenceの具体的な定義・前後の局所帰結は対象に残す。
- **除外維持** — `prose` L1340–1344: turbulenceの動機と、non-Archimedeanなlogic-action codingとの定性的比較。Hjorthの非分類定理は明示的な外部入力であり、ここでHjorth analysisやabsolutenessを再証明する箇所ではない。local orbitとturbulenceの具体的な定義・前後の局所帰結は対象に残す。
- **除外維持** — `prose` L1384–1391: turbulenceの動機と、non-Archimedeanなlogic-action codingとの定性的比較。Hjorthの非分類定理は明示的な外部入力であり、ここでHjorth analysisやabsolutenessを再証明する箇所ではない。local orbitとturbulenceの具体的な定義・前後の局所帰結は対象に残す。
- **除外維持** — `statement` L1394–1400: Hjorthの乱流定理を外部の非分類原理として使うことと、証明が本文の範囲外であることを明示する。
- **除外維持** — `prose` L1402–1409: Hjorthの外部定理の証明の文献的説明と、Becker–Kechrisの閉部分群logic-action codingの引用上の対比。両引用入力からそのような作用がturbulentでないと結論する局所的な推論はこの範囲から外し、実際のIsTurbulentAction/ClassifiableByCountableStructuresを使う補題へ接続した。
- **除外維持** — `prose` L1413–1415: 直前の局所的な否定の帰結を解釈する位置付けの一文。新しいturbulence判定・証明・分類写像を構成する箇所ではない。
- **除外維持** — `prose` L1417–1418: Hjorthの完全な定理と証明の参考文献を示すだけで、新しい局所的な証明ではない。
- **除外維持** — `prose` L1420–1421: Hjorthに引用するell^p translationのturbulent例と、Ferenczi–Louveau–Rosendal/Sabokに引用する他の非分類結果の概説。密度・meagreness・局所軌道の証明やBanach/C*-algebraのcodingをここでは展開せず、後者を未証明のturbulent例として代用しないことも明示する。
- **除外維持** — `prose` L1423–1425: Hjorthに引用するell^p translationのturbulent例と、Ferenczi–Louveau–Rosendal/Sabokに引用する他の非分類結果の概説。密度・meagreness・局所軌道の証明やBanach/C*-algebraのcodingをここでは展開せず、後者を未証明のturbulent例として代用しないことも明示する。
- **除外維持** — `prose` L1427–1431: Hjorthに引用するell^p translationのturbulent例と、Ferenczi–Louveau–Rosendal/Sabokに引用する他の非分類結果の概説。密度・meagreness・局所軌道の証明やBanach/C*-algebraのcodingをここでは展開せず、後者を未証明のturbulent例として代用しないことも明示する。
- **除外維持** — `prose` L1437–1437: Borel reducibility章との関係の総括、Glimm–Effros/HKLの歴史、Kechris–LouveauのE1の非軌道性、普遍解析同値関係、Vaught予想と文献への案内。個別の還元や反例の局所証明を追加する箇所ではなく、各引用結果・別章の実際の証明と区別する。
- **除外維持** — `prose` L1439–1464: Borel reducibility章との関係の総括、Glimm–Effros/HKLの歴史、Kechris–LouveauのE1の非軌道性、普遍解析同値関係、Vaught予想と文献への案内。個別の還元や反例の局所証明を追加する箇所ではなく、各引用結果・別章の実際の証明と区別する。
- **除外維持** — `prose` L1466–1471: 章の既述結果の整理と引用するDing--Zheng等の研究動向であり，新しい局所還元の証明を提示しない。
- **除外維持** — `prose` L1473–1474: Borel reducibility章との関係の総括、Glimm–Effros/HKLの歴史、Kechris–LouveauのE1の非軌道性、普遍解析同値関係、Vaught予想と文献への案内。個別の還元や反例の局所証明を追加する箇所ではなく、各引用結果・別章の実際の証明と区別する。

### borel-reducibility-synthesis

- **除外維持** — `prose` L3–11: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L13–17: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L19–24: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L26–30: C0(R)の表現・射影値測度・self-adjoint operatorというspectral theoremと、C*(R)のFourier同一視を用いる動機付けの標準的背景。既出のFourier transformの周波数を解釈する例であり、ここで作用素環の表現定理やそのBorel codingの局所証明は展開しない。compact self-adjointの完全不変量の局所証明は別単位で対象に残す。
- **除外維持** — `prose` L32–37: C0(R)の表現・射影値測度・self-adjoint operatorというspectral theoremと、C*(R)のFourier同一視を用いる動機付けの標準的背景。既出のFourier transformの周波数を解釈する例であり、ここで作用素環の表現定理やそのBorel codingの局所証明は展開しない。compact self-adjointの完全不変量の局所証明は別単位で対象に残す。
- **除外維持** — `prose` L39–44: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L46–61: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L65–71: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L118–123: Baire spaceからのtransferという既出の表現への概念的な比較。特定の新しい性質について任意の商写像に沿う降下を証明する文ではなく、還元で比較する方法を案内する背景である。
- **除外維持** — `prose` L215–225: 一般self-adjoint作用素の測度類不変量に関する適用限界の注意。具体的な反例・構成・証明をこの章で提示せず、後続の局所的な補題としても使用しない。直前のcompact作用素の局所証明とは別の背景説明である。
- **除外維持** — `prose` L379–383: Glimm/EffrosからHKLへの歴史的帰属と原論文への案内だけ。Borel degreeにE0より真に下のnonsmooth段階がないという直前の局所的な帰結は除外を外し、実際のHKL構成を使うe0_minimal_nonsmoothへ接続した。
- **除外維持** — `prose` L385–394: Glimm/Effrosに引用するseparable C*-algebraのirreducible representationsとtype Iの標準分類結果、およびHKLの適用例。表現空間のBorel codingやtype-I定理の証明をこの章で提示せず、局所的なHKLとそのstrict-threshold帰結は別途対象に戻している。
- **除外維持** — `prose` L398–405: 直後に述べるSilver dichotomyへの導入と歴史的帰属・出典表示。Silverの定理と局所的な証明は別に対応済み。
- **除外維持** — `prose` L442–446: Silver/HKLの専門的証明への読む順序と、実パラメータを保つrelativizationの意味を説明する道案内。ここで新しいlightface codeや融合木を構成するものではなく、後章のboundedness・generic pair splitting・witnessを保持したfusion・双方向還元の実際の証明を対象に残す。
- **除外維持** — `prose` L448–450: Silver/HKLの専門的証明への読む順序と、実パラメータを保つrelativizationの意味を説明する道案内。ここで新しいlightface codeや融合木を構成するものではなく、後章のboundedness・generic pair splitting・witnessを保持したfusion・双方向還元の実際の証明を対象に残す。
- **除外維持** — `prose` L452–452: Silver/HKLの専門的証明への読む順序と、実パラメータを保つrelativizationの意味を説明する道案内。ここで新しいlightface codeや融合木を構成するものではなく、後章のboundedness・generic pair splitting・witnessを保持したfusion・双方向還元の実際の証明を対象に残す。
- **除外維持** — `prose` L454–461: Silver/HKLの専門的証明への読む順序と、実パラメータを保つrelativizationの意味を説明する道案内。ここで新しいlightface codeや融合木を構成するものではなく、後章のboundedness・generic pair splitting・witnessを保持したfusion・双方向還元の実際の証明を対象に残す。
- **除外維持** — `prose` L463–466: Silver/HKLの専門的証明への読む順序と、実パラメータを保つrelativizationの意味を説明する道案内。ここで新しいlightface codeや融合木を構成するものではなく、後章のboundedness・generic pair splitting・witnessを保持したfusion・双方向還元の実際の証明を対象に残す。
- **除外維持** — `prose` L490–491: Feldman–MooreをKechris §18/Gao Ch.7/Feldman–Moore 1977から明示的に引用する外部定理として扱う。Lusin–Novikov、部分全単射の分割、involutionsの生成群という文は引用する証明の構成方針の要約で、全てのBorel graphingの補助構成をこの章で展開したとは扱わない。章のproof-scopeもこの定理を外部入力と明示している。
- **除外維持** — `statement` L493–498: Feldman–MooreをKechris §18/Gao Ch.7/Feldman–Moore 1977から明示的に引用する外部定理として扱う。Lusin–Novikov、部分全単射の分割、involutionsの生成群という文は引用する証明の構成方針の要約で、全てのBorel graphingの補助構成をこの章で展開したとは扱わない。章のproof-scopeもこの定理を外部入力と明示している。
- **除外維持** — `prose` L500–507: Feldman–MooreをKechris §18/Gao Ch.7/Feldman–Moore 1977から明示的に引用する外部定理として扱う。Lusin–Novikov、部分全単射の分割、involutionsの生成群という文は引用する証明の構成方針の要約で、全てのBorel graphingの補助構成をこの章で展開したとは扱わない。章のproof-scopeもこの定理を外部入力と明示している。
- **除外維持** — `prose` L509–510: Feldman–MooreをKechris §18/Gao Ch.7/Feldman–Moore 1977から明示的に引用する外部定理として扱う。Lusin–Novikov、部分全単射の分割、involutionsの生成群という文は引用する証明の構成方針の要約で、全てのBorel graphingの補助構成をこの章で展開したとは扱わない。章のproof-scopeもこの定理を外部入力と明示している。
- **除外維持** — `prose` L512–514: 記述集合論・可測力学・幾何群論の関係を述べる分野上の位置付けだけで、数学的な局所証明ではない。
- **除外維持** — `prose` L589–601: Adams--Kechris，Jackson--Kechris--Louveau，Borel漸近次元等の引用結果を比較する概説であり，これらの証明は局所義務に含めない。
- **除外維持** — `prose` L603–607: 滑らかさ・超有限性・普遍性という既述の尺度を要約する節末のまとめである。
- **除外維持** — `prose` L611–615: E1の非軌道性、Hjorthの非分類、普遍解析同値関係、Banach/C*-algebraの完全性という引用付きの大域的分類結果と参考文献の概説。個別のcoding・rigidity・completenessの局所証明を展開せず、E0および還元の基本的な局所証明は対象に残す。
- **除外維持** — `prose` L617–634: E1・turbulence・普遍解析同値関係等の引用された分類指標を列挙する概説である。
- **除外維持** — `prose` L636–638: E1の非軌道性、Hjorthの非分類、普遍解析同値関係、Banach/C*-algebraの完全性という引用付きの大域的分類結果と参考文献の概説。個別のcoding・rigidity・completenessの局所証明を展開せず、E0および還元の基本的な局所証明は対象に残す。
- **除外維持** — `prose` L644–648: separable Banach spacesを用いた外部理論のケーススタディ。C([0,1])への標準的な等長埋め込みとEffros coding・解析性を背景として述べ、Ferenczi–Louveau–Rosendalのuniversalityを明示的に引用する。ここではBanach空間の埋め込み・coding・isomorphism witnessesの局所的な構成や証明を展開しない。
- **除外維持** — `prose` L650–653: separable Banach spacesを用いた外部理論のケーススタディ。C([0,1])への標準的な等長埋め込みとEffros coding・解析性を背景として述べ、Ferenczi–Louveau–Rosendalのuniversalityを明示的に引用する。ここではBanach空間の埋め込み・coding・isomorphism witnessesの局所的な構成や証明を展開しない。
- **除外維持** — `prose` L655–664: separable Banach spacesを用いた外部理論のケーススタディ。C([0,1])への標準的な等長埋め込みとEffros coding・解析性を背景として述べ、Ferenczi–Louveau–Rosendalのuniversalityを明示的に引用する。ここではBanach空間の埋め込み・coding・isomorphism witnessesの局所的な構成や証明を展開しない。
- **除外維持** — `prose` L669–673: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。
- **除外維持** — `prose` L675–681: 章・部の動機、前提、読む順序、証明範囲と後続章への案内。還元の合成・complete invariants・E0非平滑性・二分法の局所的な証明は対象に残す。Feldman–Moore、DJK、専門的分類の外部入力と、後章で実際に証明するSilver/HKLの構成を区別する。

### forcing-polish-spaces

- **除外維持** — `prose` L3–8: 章の主題を位相・測度・独立性の関係として紹介する総説。具体的なCohen/random条件、内部符号、generic realの構成、回避定理、局所的なabsolutenessの証明は個別の対象に残し、導入の大域的なregularity概説自体を新しい局所定理とは扱わない。
- **除外維持** — `prose` L10–14: 章の主題を位相・測度・独立性の関係として紹介する総説。具体的なCohen/random条件、内部符号、generic realの構成、回避定理、局所的なabsolutenessの証明は個別の対象に残し、導入の大域的なregularity概説自体を新しい局所定理とは扱わない。
- **除外維持** — `prose` L16–21: Cohenの歴史と、組合せ的条件・名前と意味論という二層の学習上の説明。有限情報はPolish-space例の直観であり、一般の強制条件を有限集合に制限する定義ではない。実際のforcing notion、名前の再帰、意味論と再帰forcingの同値は付録の定義・証明を参照する構成で、それらの局所的な内容をこの案内だけで免除しない。
- **除外維持** — `prose` L23–23: Cohenの歴史と、組合せ的条件・名前と意味論という二層の学習上の説明。有限情報はPolish-space例の直観であり、一般の強制条件を有限集合に制限する定義ではない。実際のforcing notion、名前の再帰、意味論と再帰forcingの同値は付録の定義・証明を参照する構成で、それらの局所的な内容をこの案内だけで免除しない。
- **除外維持** — `prose` L25–29: Cohenの歴史と、組合せ的条件・名前と意味論という二層の学習上の説明。有限情報はPolish-space例の直観であり、一般の強制条件を有限集合に制限する定義ではない。実際のforcing notion、名前の再帰、意味論と再帰forcingの同値は付録の定義・証明を参照する構成で、それらの局所的な内容をこの案内だけで免除しない。
- **除外維持** — `prose` L31–33: Cohenの歴史と、組合せ的条件・名前と意味論という二層の学習上の説明。有限情報はPolish-space例の直観であり、一般の強制条件を有限集合に制限する定義ではない。実際のforcing notion、名前の再帰、意味論と再帰forcingの同値は付録の定義・証明を参照する構成で、それらの局所的な内容をこの案内だけで免除しない。
- **除外維持** — `prose` L35–39: 既存の付録への読む順序、可算推移的ground modelと外部generic filterの規約、Borel符号の旧モデルと拡大での解釈、および外部入力と局所証明の範囲を明示する案内。特に内部の測度値と旧実数だけの可算な外部集合の測度を同一視しない。実際のコードの絶対性とgeneric truthの証明は参照先に残す。
- **除外維持** — `prose` L41–44: 既存の付録への読む順序、可算推移的ground modelと外部generic filterの規約、Borel符号の旧モデルと拡大での解釈、および外部入力と局所証明の範囲を明示する案内。特に内部の測度値と旧実数だけの可算な外部集合の測度を同一視しない。実際のコードの絶対性とgeneric truthの証明は参照先に残す。
- **除外維持** — `prose` L46–49: 既存の付録への読む順序、可算推移的ground modelと外部generic filterの規約、Borel符号の旧モデルと拡大での解釈、および外部入力と局所証明の範囲を明示する案内。特に内部の測度値と旧実数だけの可算な外部集合の測度を同一視しない。実際のコードの絶対性とgeneric truthの証明は参照先に残す。
- **除外維持** — `prose` L51–55: 既存の付録への読む順序、可算推移的ground modelと外部generic filterの規約、Borel符号の旧モデルと拡大での解釈、および外部入力と局所証明の範囲を明示する案内。特に内部の測度値と旧実数だけの可算な外部集合の測度を同一視しない。実際のコードの絶対性とgeneric truthの証明は参照先に残す。
- **除外維持** — `prose` L65–72: 既存の付録への読む順序、可算推移的ground modelと外部generic filterの規約、Borel符号の旧モデルと拡大での解釈、および外部入力と局所証明の範囲を明示する案内。特に内部の測度値と旧実数だけの可算な外部集合の測度を同一視しない。実際のコードの絶対性とgeneric truthの証明は参照先に残す。
- **除外維持** — `prose` L206–209: disjunctivenessと測度論的ランダム性の違いを述べる動機付けの背景。計算可能な具体例やその生成法・計算性の局所証明はこの段落で提示せず、以後の強制法の構成もこの比較に依存しない。直前で実際に示す各word requirementの稠密開性とcomeager性は除外から戻し、cohen_disjunctive_residualの可算交叉の証明へ接続した。lambdaで計算可能なdisjunctive列の構成を形式化済みとは扱わない。
- **除外維持** — `prose` L336–342: 直後のfilter realとBorel truthの証明への導入。固定した宇宙で明示的仮定を用いるという読み方の案内で、追加の数学的命題ではない。
- **除外維持** — `prose` L456–464: 内部商・正条件・比較写像およびfilterの輸送を構成する付録節への明示的参照。新しい局所証明を提示せず、以後で用いる構成を指定している。
- **除外維持** — `prose` L561–567: Kechris Theorem 17.9を明示的に引用するcylinder版Lebesgue密度定理の外部入力。正規化円筒測度の定義は除外から戻してbinary_cylinderDensityへ接続し、例外集合の内部符号の構成とgeneric回避による局所的な密度点の帰結は既存の対象に残す。密度定理そのものを形式化済みとは扱わない。
- **除外維持** — `prose` L617–622: 直前に証明した内部deviation codeとLebesgue密度点の命題、およびCohen/randomの比較表の導入としての総括。密度定理そのものの引用と、そのnull例外集合をgenericが避ける局所証明を区別し、追加の密度点定理や別の計算モデルを主張する箇所ではない。
- **除外維持** — `prose` L624–624: Mantheの検証済みMartin証明を参照する証明方針の紹介である。局所的な戦略の定義間の移送は別の補題とLean対応で確認している。
- **除外維持** — `prose` L637–640: Cohen/randomのBoolean完備化とmeager/null idealsの大域的な非対称性に関する背景上の注意。完備化の同型・非同型の具体的な証明や後続の局所証明で使う反例をこの章では展開しない。Boolean評価とCohen完備化を構成する別課題ASTRA-COV-004を解消済みとは扱わない。
- **除外維持** — `prose` L708–711: absolutenessの意味と、記述的複雑性・forcing invarianceを比較する節の導入と総括。個別のanalytic/coanalyticとShoenfieldの命題・証明を対象に残す。
- **除外維持** — `prose` L713–722: Shoenfieldの後続の局所的な証明の紹介と、proper class of Woodin cardinalsを仮定するWelch Theorem 3.20のgeneric absolutenessの引用。Woodinの外部定理をMartin–Steel determinacyの証明から導いたとは扱わず、その大域的な証明をここでは提示しない。後続の基底定理からのShoenfieldの局所的な演繹は別途対象である。
- **除外維持** — `prose` L724–725: absolutenessの意味と、記述的複雑性・forcing invarianceを比較する節の導入と総括。個別のanalytic/coanalyticとShoenfieldの命題・証明を対象に残す。
- **除外維持** — `proof` L787–789: 旧モデルにない新しい実数の証人を除くため、直後で明示的に引用するKondo–Addison基底定理を使うという証明上の道案内。その基底定理の証明も新しい証人選択アルゴリズムもこの文では構成しない。
- **除外維持** — `statement` L791–794: Kondo–Addisonの構成可能な証人の存在は本文が明示的に外部入力と区別している。後続のShoenfieldへの適用は別の対象である。
- **除外維持** — `proof` L796–800: Kondo–Addison基底定理をcoanalytic kernel A_aの記号で言い直した外部入力、およびcoanalytic boundednessだけではconstructible witnessを選べないという適用範囲の説明。本文はKechris §35/Moschovakis Ch.4を引用して独立した基底定理の証明と区別している。後続のL[a]の一致とcoanalytic absolutenessからの演繹は対象に残す。
- **除外維持** — `proof` L802–807: Kondo–Addison基底定理をcoanalytic kernel A_aの記号で言い直した外部入力、およびcoanalytic boundednessだけではconstructible witnessを選べないという適用範囲の説明。本文はKechris §35/Moschovakis Ch.4を引用して独立した基底定理の証明と区別している。後続のL[a]の一致とcoanalytic absolutenessからの演繹は対象に残す。
- **除外維持** — `prose` L828–831: 既に述べたabsolutenessと後述する高階の独立性を比較する説明上の結語。新しいforcingやregularity反例の構成を提示する文ではない。
- **除外維持** — `prose` L834–846: MM++からWoodinの(*)へのAsperó--Schindlerの外部結果を紹介する展望であり，局所forcing構成の未明示の証明段階ではない。
- **除外維持** — `prose` L850–852: genericという言葉を位相と測度の観点で説明する導入と結語。間にあるCohen genericのdense-open/meager characterizationとrandom genericのnull回避という数学的な主張は引き続き対象として接続を確認する。
- **除外維持** — `prose` L866–869: genericという言葉を位相と測度の観点で説明する導入と結語。間にあるCohen genericのdense-open/meager characterizationとrandom genericのnull回避という数学的な主張は引き続き対象として接続を確認する。
- **除外維持** — `prose` L1215–1217: regularityの独立性に関する既出結果・外部結果を比較する節の案内。具体的な局所構成の証明をこの導入だけで免除しない。
- **除外維持** — `prose` L1219–1224: analyticのregularityは既出節への明示的参照であり、Lのprojective well-orderとSolovayモデルはKunen等に基づく外部の構成可能性・相対無矛盾性の概説。ここではそれらのモデルの構成やwell-orderのprojective codingの証明を展開しない。次段落の具体的なVitali selectorの局所構成と非正則性は別の未確認対象に残す。
- **除外維持** — `prose` L1235–1240: Solovay 1970から明示的に引用する、inaccessibleからのLevy collapseと内モデルのregularity定理、およびそのhomogeneity/real parameter依存の説明。モデル構成・パラメータ反映・homogeneityによる全regularityの証明は引用する外部定理で、cccだけからの局所的な帰結として主張していない。
- **除外維持** — `prose` L1242–1246: Solovay 1970から明示的に引用する、inaccessibleからのLevy collapseと内モデルのregularity定理、およびそのhomogeneity/real parameter依存の説明。モデル構成・パラメータ反映・homogeneityによる全regularityの証明は引用する外部定理で、cccだけからの局所的な帰結として主張していない。
- **除外維持** — `prose` L1248–1253: Shelah 1984のinaccessible consistency strength下界とSolovayの上界によるequiconsistencyを引用するメタ数学的な背景。BPだけの強さと混同しないという注意を含み、ここでinner modelの下界証明を展開しない。
- **除外維持** — `prose` L1255–1256: determinacy章で扱うprojective determinacyとregularityの関係への概念的な比較。新しいゲーム・戦略やPDの無矛盾性をこの一文で構成していない。

### effective-dst-lightface-hierarchies

- **除外維持** — `prose` L5–11: boldfaceとlightfaceという本章の主題と、古典的理論の計算論的な精密化の導入。具体的な効果的開集合・木・階層の演算の定義は後続の対象に残し、この総説自体を新しい形式的な階層構成とは扱わない。
- **除外維持** — `prose` L28–32: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L34–39: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L45–45: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L55–59: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L63–69: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L75–76: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L78–86: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L88–92: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L94–97: 三章への分担、読む順序、前提、証明範囲と後続のSilver/HKLの構成への案内。実際の木・順序数記法・jump・共通bound・rank・融合の命題と証明は対応する章で対象に残す。ここでは参照先の定理を新たに局所証明したとも、任意の無限証人を計算可能に選択できるとも主張していない。
- **除外維持** — `prose` L332–335: 直前のsection-tree testをランク理論で使うという読者への道案内。coanalytic集合の補射影から、同じパラメータを保つ実際のlambda-decided section treeとwell-foundednessの同値を得る数学的な部分は除外から戻してcoanalytic_section_treeへ接続した。ランクを求める新しいアルゴリズムをこの段落で構成してはいない。
- **除外維持** — `prose` L340–343: Kleeneの木という後の明示的な文献引用例と、well-foundednessのPi11完全性を証明する次章への参照に基づく適用範囲の警告。ここで新しい木・非計算可能性のreduction・totality deciderを構成する局所的な議論は展開しない。既出の木の恒等式だけから不可能性を証明済みとは扱わず、実際の完全性の証明は参照先に残す。
- **除外維持** — `prose` L761–769: 点類記号のambient Baire spaceと固定する実パラメータ、realという語、有限列の標準的codingとsyntax indexの規約を指定する説明。standard-Borel intercodabilityは既出の表現への背景的な参照で、任意のBorel同型によるcomputability保存を主張しない。具体的な点類の定義とcoding選択の不変性はこの除外から分け、パラメータを保つlambda行列と明示的なcode変換へ接続する。
- **除外維持** — `prose` L771–772: 点類記号のambient Baire spaceと固定する実パラメータ、realという語、有限列の標準的codingとsyntax indexの規約を指定する説明。standard-Borel intercodabilityは既出の表現への背景的な参照で、任意のBorel同型によるcomputability保存を主張しない。具体的な点類の定義とcoding選択の不変性はこの除外から分け、パラメータを保つlambda行列と明示的なcode変換へ接続する。
- **除外維持** — `prose` L801–802: 直後の具体例を古典的位相と比較するという短い導入だけ。computable singletonとcomputable pointsの可算性・非閉性はこの導入の除外に含めず、実際のlambda programsと証明へ接続した。
- **除外維持** — `prose` L867–872: 固定する実パラメータの役割を、後続のGandy–Harrington条件とTTEの無パラメータの計算性へ結び付ける読む順序の説明。有限Borel/projective階層の全段階のboldface/lightface同値は直前の対象として分け、一つの開行列・一つの共通パラメータと実際のlambda accessorsによる比較へ接続する。この段落自身は新たな可算符号や証人の選択手続きを構成しない。
- **除外維持** — `prose` L878–880: universal setと対角化をこの節で行うという導入。effectively open/analyticの実際のuniversal familyと対角化、および有限の全正段階の一様な行列によるuniversalityと対角化は対象として分け、実際の構成へ接続する。この導入自身は追加の計算や別の分類定理を構成しない。
- **除外維持** — `prose` L972–975: universal setsが分類理論で使われる理由を説明する動機と後続章への案内。特定の分類不変量について新しい非分類reductionや対角化をここで提示する箇所ではない。
- **除外維持** — `prose` L982–992: hyperarithmeticをlightface版のBorelとして位置付ける背景説明と、後続3構成およびlambdaモデルの命名規約の案内。局所的に新しい同値定理や構成を主張する箇所ではない。実際のjump・記法・反復の定義と証明は各後続箇所で監査する。
- **除外維持** — `prose` L1388–1390: Moschovakis/Mansfield–Weitkampに明示的に引用するKleene OのPi11完全性の外部入力。本文も後のwell-founded tree codesの完全性からの帰結とは区別する。既存のnotation validity、ordinal interpretationやWF-tree reductionだけでこの完全性を証明済みとは扱わない。
- **除外維持** — `prose` L1452–1456: 同じ順序数を表す異なる記法のiterated jumpsを比較するSpectorの一意性定理を、Moschovakis/Mansfield–Weitkampに明示的に引用する外部入力。同一記法の意味の一意性と区別されており、局所のvalue_uniqueから別記法のoracle比較を導いたとは扱わない。
- **除外維持** — `prose` L1589–1592: 古典的なBorel構成のeffectivizationに必要なデータを説明する診断上の注意と章の結語。一般の古典的証明からrecursive codeやcomputable witnessを一様に抽出する手続きをこの文章で構成してはいない。直前のcodeの全体ランク上界は局所的に証明する対象として残し、実際のrecursiveBorel_code_rank_lt_boundに接続した。
- **除外維持** — `prose` L1624–1628: true-stage法とその引用された応用を概説する。本文の局所構成に新しいpriority argumentや高階情報の計算を持ち込まない。
- **除外維持** — `prose` L1630–1633: true-stage法とその引用された応用を概説する。本文の局所構成に新しいpriority argumentや高階情報の計算を持ち込まない。
- **除外維持** — `prose` L1635–1640: true-stage法とその引用された応用を概説する。本文の局所構成に新しいpriority argumentや高階情報の計算を持ち込まない。
- **除外維持** — `prose` L1642–1643: 古典的なBorel構成のeffectivizationに必要なデータを説明する診断上の注意と章の結語。一般の古典的証明からrecursive codeやcomputable witnessを一様に抽出する手続きをこの文章で構成してはいない。直前のcodeの全体ランク上界は局所的に証明する対象として残し、実際のrecursiveBorel_code_rank_lt_boundに接続した。

### effective-dst-ranks-effective-refinements

- **除外維持** — `prose` L4–5: EDSTの位置付けを導入する見出し相当の一文。追加命題や局所証明ではない。
- **除外維持** — `prose` L7–14: classical DST・recursion theory・TTEという前提分野の概観。名前による計算の局所的な逆像論証は別段落を対象に戻したので、この一覧に巻き込んで除外しない。
- **除外維持** — `prose` L20–23: 実現可能性への読書案内、相対化の位置付け、および標準文献の紹介。局所的な構成や証明を提示しない。
- **除外維持** — `prose` L40–43: 前章・本章の構成を紹介する概要だけ。列挙した個々の構成は本文の独立した項目として監査する。
- **除外維持** — `prose` L45–49: 後続章への道案内と、外部引用であるKondo--Addison・Spector--Gandyの位置付け。ここに新しい証明ステップはない。
- **除外維持** — `prose` L53–61: 前提事項、学習順序、プログラムを確認する参照先の案内。数学的主張の証明をこの段落で提示していない。
- **除外維持** — `prose` L67–73: boundednessの役割を述べる導入・動機付け。定理は直後で別に提示され、ここは追加の局所証明を主張しない。
- **除外維持** — `prose` L178–189: boundednessの後続用途への参照と定性的なスローガンの説明。新しい構成や精密な追加命題を証明する箇所ではなく、具体的な定理・適用は参照先で監査する。
- **除外維持** — `prose` L191–201: 後続のseparation・rank approximation・dichotomy節への道案内。列挙した各構成をこの段落で新たに証明するという主張ではない。
- **除外維持** — `prose` L205–211: 後続のbasis・norm・separationの構成を導入する動機付けだけで、追加命題や証明ステップを提示していない。
- **除外維持** — `prose` L337–342: 次のseparation形を紹介する一文だけ。命題と証明は直後の独立した監査対象。
- **除外維持** — `prose` L371–378: Kondo--Addisonのconstructible witnessを外部の専門定理として引用する段落。局所的なrank構成だけでこの外部定理を証明したとは扱わない。
- **除外維持** — `prose` L380–388: 後続のdichotomy証明が用いる道具と依存しない外部道具を説明する案内。ここで新たなseparator構成やfusion命題を提示していない。
- **除外維持** — `prose` L685–693: 直前の外的Borel-expression completeness定理の適用範囲についての注意。任意のcode選択を固定パラメータでの計算可能な選択と同一視しないと説明しており、具体的な非計算可能例の局所証明ではない。
- **除外維持** — `prose` L1033–1040: 次の構成がlabel streamを読み、任意のprogram indexには有限の計算証明を用いることを紹介する方法上の案内。構成と証明は後続の独立した項目で監査する。
- **除外維持** — `prose` L1236–1245: countable modelによる古典forcingの別証明方針を付録へ明示的に参照し、ここで採用するlocal-truth testsとの関係を説明する。generic extensionの構成をこの段落で主張していない。
- **除外維持** — `prose` L1363–1370: classicalとeffectiveな定理の違いを紹介する一般的な導入で、特定の追加定理や計算手続きを証明していない。
- **除外維持** — `prose` L1372–1380: 後続の短いカタログと計算章への読書案内。各数学的主張は対応する後続の命題・証明・本文で個別に監査する。
- **除外維持** — `prose` L1995–2000: Spector--Gandyの背景であるconstructible hierarchyとadmissible setの標準的定義・外部事実を紹介する部分。後続の明示的文献引用に属し、本章の局所構成や証明対象ではない。
- **除外維持** — `prose` L2002–2002: 直後に引用するSpector--Gandy定理を紹介する一文だけ。
- **除外維持** — `statement` L2004–2012: Spector–Gandyとadmissible-set理論をMansfield–Weitkampから引用し、本文でその証明を与えていない。
- **除外維持** — `prose` L2014–2019: Spector--Gandyの点ごとの相対化と適切なadmissible structureについての外部理論の説明で、Mansfield--Weitkamp Ch.5を明示的に参照する。局所証明は与えていない。

### effective-dst-gandy-harrington-dichotomies

- **除外維持** — `prose` L4–7: 本章で証明するSilver/HKLと、その前提となる章の案内。ここ自体は追加の局所証明を提示しない。
- **除外維持** — `prose` L9–13: GH topology・Silver/HKL・local truthの役割を概観する導入。本文の具体的な構成と証明は独立に監査済みで、この段落には新しい命題や証明ステップがない。
- **除外維持** — `prose` L17–23: 前提事項、読み進める順序、確認すべき道具を示す学習案内。新しい構成をこの段落で与えていない。
- **除外維持** — `prose` L30–39: Silver/HKLの共通topologyを次に構成するという導入。定義と個々のtopological factsは後続の独立した監査対象。
- **除外維持** — `prose` L132–142: Harrington/HKLの証明方針とKanoveiへの文献案内。local truth、kernel、fusionは後続で局所的に証明しており、この段落で追加のforcing theoremを主張しない。
- **除外維持** — `prose` L144–154: 固定パラメータの規約と、Silver/HKLを一般Polish空間へ移す後続手順の道案内。parameter構成とsurjection/closed-presentationによる移送の定理は対応する証明箇所で監査する。
- **除外維持** — `prose` L156–161: 既に構成したcommon-parameterとuniform codesの節への参照だけ。
- **除外維持** — `prose` L211–216: 直後の2つの帰結を紹介する一文だけ。
- **除外維持** — `prose` L421–429: 有限のpresentation操作と、dense refinement・fusion witnessの選択を区別する証明範囲の説明。有限操作のlambdaプログラムと連続antichainの存在は既存の構成・定理に対応し、この段落は新たな計算可能な選択やその不可能性を主張しない。
- **除外維持** — `prose` L431–439: 直前に完成したSilver antichainと後続のdichotomyへの接続を説明するまとめ。Borel近似をequivalence relationと扱わない等の注意も証明手順の説明で、追加命題ではない。
- **除外維持** — `prose` L895–899: 次PartのTTE・computable analysis・randomness・Weihrauch章への概要と道案内だけ。
- **除外維持** — `prose` L901–906: 次Partのdomain theory・realizability・effective toposおよび必要な前提章の案内。局所的な数学的構成や証明をここで提示していない。

### computable-polish-spaces-tte

- **除外維持** — `prose` L4–9: TTEの名前・問い合わせ・realizerの考え方を導入する総論であり，後続と別の実装を要求しない。
- **除外維持** — `prose` L11–16: 後続章への案内と、この章で扱う情報の種類の概観。具体的な定義・反例・構成は本文の対応済み箇所で別途監査する。
- **除外維持** — `prose` L25–32: 前章のCauchy表現と本章の実効性の条件を予告する章の概観。距離データ・球の半決定・有限入力使用の個別の定義と証明は後続で別途監査する。ここで独立のアルゴリズムを定義してはいない。
- **除外維持** — `prose` L38–43: 章内の読む順序と後続章の前提を示す案内。新しい数学的定義・命題・局所証明はない。
- **除外維持** — `prose` L45–58: 読者の前提知識と付録の読む順序を説明する案内。各lambda構成の証明は参照先で別途監査し、この案内を新たな局所定理として数えない。
- **除外維持** — `prose` L60–68: 有限データ操作・pairing・tagging・finite trialの証明の所在を示す案内。操作の正しさの主張は後続の各定理と付録で別途監査する。
- **除外維持** — `prose` L82–88: 読者の前提知識と参照先、学習目標を示す案内。forcingやeffective DSTへの非依存性は読む順序の説明である。
- **除外維持** — `statement` L134–138: 入力-query合流性の再掲。元の付録の合流性の証明と本章の有限使用性・連続実現子の議論はそれぞれ別途監査する。
- **除外維持** — `prose` L221–225: 直前で証明した連続実現子の特徴付けの意味を説明する文章。人工的な連続性という表現は新しい性質の定義や独立した命題ではない。
- **除外維持** — `prose` L270–272: 付録にある演算の所在を示す案内。数・有理数・リスト・有限表作成の実際の性質を述べる後続4段落は除外を解除し、対応するlambda項の定理に接続した。
- **除外維持** — `prose` L638–644: 空間構成を読むための案内。valid namesと表現値を確認するという作業方針で、独立した数学的主張や構成はここにはない。
- **除外維持** — `prose` L1076–1080: effective toposとTTEの指数対象を比較する背景説明。ここで両者の同一視や新しい指数構成を主張せず、具体的なTTE指数の証明は直前で別途監査する。
- **除外維持** — `prose` L1252–1260: 直後のeffective-basis lemmaとmargin lemmaの位置付け・引用を述べる導入。両補題の定義・主張・証明はそれぞれ別途監査する。

### computable-analysis

- **除外維持** — `prose` L3–7: 章全体の方針と入力表現の役割を説明する導入。ここでは独立した構成や証明を提示せず、具体的な実現子と表現の性質は後続の各結果で別途監査する。
- **除外維持** — `prose` L9–14: 章内の構成と後続章への案内。個別のコンパクト性・測度・積分の定義と証明は後続で別途監査する。
- **除外維持** — `prose` L18–26: 前提知識、参照先、読む順序と学習目標を示す案内。新たな数学的定義・命題・局所証明を含まない。
- **除外維持** — `prose` L463–467: 古典的なコンパクト性と実効的な入力データを区別する注意。ここでは特定の悪い表示や閉集合の反例を構成せず、後続もその具体的反例に依存しない。局所証明を伴わない比較・背景として対象外とする。
- **除外維持** — `prose` L937–942: 前の分類の章への概念的な参照。Borel分類と計算可能性を同一視せず、この章でC0代数の分類を再証明しない。最後のL1からFourierへの計算可能性は直後の主定理とfourier_hasComputableRealizerで別途監査する。
- **除外維持** — `prose` L950–953: Faris Theorem 9.16の密度定理を明示的に外部入力として引用する箇所。複素数値での実部・虚部への適用もその標準的入力の説明。続く有理区間ステップ関数による近似の構成は本文とLeanで別途監査する。
- **除外維持** — `prose` L1438–1444: Kunkleを明示引用するL2 Fourierユニタリと逆の計算可能性の外部結果。この章の局所構成はL1から局所一様表現への変換であり、L2の作用素論的証明は提示も使用もしていない。

### algorithmic-randomness

- **除外維持** — `prose` L5–12: 前提知識と読む順序を示す導入。3種類のテストの定義・包含・分離と最終点の非計算可能性は、この章の対応済み箇所で別途監査する。
- **除外維持** — `prose` L21–24: 前章のrandom forcingと、この章で定義する計算可能な零集合テストの概念的な比較。ground-model Borel codesを扱う新しい局所構成や同値定理はなく、ML・weak2・Schnorrの個別定義は直後で別途監査する。
- **除外維持** — `prose` L51–55: 評価による計算可能測度と、有理数上界付きの有界計算可能連続関数の積分の計算可能性との同値を、Hoyrup–Rojasからの外部定理として明記して引用する箇所。一般の計算可能Polish確率空間でのMLテストの局所定義は除外を解除し、lambdaによる行列挙と同じ確率測度に接続した。
- **除外維持** — `prose` L500–501: 3種類の零集合回避の概念を比較する表の導入または章の位置付け。forcingとalgorithmic randomnessを同一視する新しい命題は提示しておらず、各ランダム性の包含と真の差は本文の個別定理で別途監査する。
- **除外維持** — `prose` L509–512: 3種類の零集合回避の概念を比較する表の導入または章の位置付け。forcingとalgorithmic randomnessを同一視する新しい命題は提示しておらず、各ランダム性の包含と真の差は本文の個別定理で別途監査する。

### weihrauch-reducibility

- **除外維持** — `prose` L5–11: 前提知識と学習目標、参照先の案内。名前の表現・還元の定義・LPOの具体的構成は後続で別途監査する。次数や比較表の全lattice理論をここでは証明しないことを明記する。
- **除外維持** — `prose` L19–24: Wadge・Borelとの概念的な比較と、多値問題を扱う動機付け。具体的なWeihrauch還元の数学的定義は後続のlambdaによる定義と表現された問題の名前への接続で別途監査する。
- **除外維持** — `prose` L51–53: 添字のroman/italicと参照先を区別する表記の説明。異なる数学的対象を比較する記号だという編集上の注意であり、新しい命題・証明ではない。
- **除外維持** — `prose` L55–56: 既に導入されたWadge・Borel・Weihrauch還元を比較する表の導入。ここで新たな相互還元・同値・lattice定理は主張しておらず、各定義は対応箇所で別途監査する。
- **除外維持** — `prose` L64–69: closed choice・compact choice・limit・unique choiceおよびIVT・最大値定理・WKLを文献上のランドマークとして挙げる概観。ここではその間の特定の還元・同値や非計算可能性を証明したとは主張しない。局所対象であるLPOから自然数閉選択への具体的還元は除外していない。
- **除外維持** — `prose` L190–200: perfect-set問題の表現依存のWeihrauch次数分類は明示的に引用文献へ委ねる。局所のCantor--Bendixson構成の追加段階ではない。
- **除外維持** — `prose` L202–211: Kiharaの相対実現可能性と不完全情報ゲームによる関連を引用している。通常の一回呼出し次数との同一視や新規モデル構成は主張していない。

### domain-theory-quasi-polish-spaces

- **除外維持** — `prose` L4–7: 章全体の比較を振り返る導入。TTEの名前と有限情報の鎖を同じ位相内容へ結ぶ局所構成・admissibility・実数Cauchy表現との連続同値は本文の個別箇所で別途Leanに対応させている。ここに追加の局所定理や計算可能な相互翻訳の主張はない。
- **除外維持** — `prose` L9–13: 非Hausdorffな計算空間と準Polish理論を位置付ける章の概観。一般化Borel理論の広い拡張は後段でde Brechtの外部理論として引用され、分離性の局所主張は本文のScott位相の証明として監査する。
- **除外維持** — `prose` L15–24: 領域理論の歴史と準Polish空間を導入する動機付け。有限観測性を実効的半決定と区別するよう修正済みで、Scott位相のT₀性・最小元をもつ非自明な場合の非T₁性は本文の別箇所で証明している。一般的な分類理論は引用された背景である。
- **除外維持** — `prose` L26–29: 章が局所証明と外部参照を併せて扱うという対象範囲の説明。定理や新しい構成ではない。外部参照という語を根拠に局所証明まで除外せず、区間反例と第2Borel階層の一致は除外を解除して接続した。
- **除外維持** — `prose` L31–35: 各節をどの順に読むかを示す章案内。interval domainとTTEの比較は案内先の個別構成で別途対応済みであり、この段落自体に新しい数学的主張はない。
- **除外維持** — `prose` L39–45: 前提節・任意の発展事項・読む順序・学習目標を列挙する読書案内。新しい命題や局所証明はない。
- **除外維持** — `prose` L55–57: 表示的意味論を紹介する導入で、型・再帰・有限近似の対応を動機付けとして予告する。プログラムの意味を割り当てる新しい定義や言語モデルの構成は展開していない。
- **除外維持** — `prose` L59–67: Abramsky–Jungを参照する表示的意味論の概説。型と関数domain、Scott連続写像のKleene最小不動点、way-belowの解釈を標準的な背景として挙げ、ここで局所的な再帰言語の意味論や最小不動点の証明を展開・後続で使用していない。flat domainとway-belowの本章で使う具体的構造は後段で別途形式化されている。
- **除外維持** — `prose` L69–71: 領域理論と関数型言語・計算可能解析の歴史的な位置付けをAbramsky–Jungに帰属させる引用付きの説明。ここで別の実行モデルや計算可能性の同値を定義しない。
- **除外維持** — `prose` L77–88: 情報の近似順序として領域理論を導入する意味論上の読み方と動機付け。新しい数学的定義・構成・証明ではなく、有向性・dcpo・way-belowの厳密な定義は直後の別単位でLeanへ接続済み。
- **除外維持** — `prose` L167–173: 直後の有限観測性の説明を導入する案内文「The slogan is:」のみ。有限観測性の数学的内容はdomain_scott_observableへ別途接続済み。
- **除外維持** — `prose` L283–289: 直後のinterval domainの性質一覧を導入する「Properties:」のみ。極大元・位相・可算基底の数学的内容は一覧の各部分で別途対応させる。
- **除外維持** — `prose` L399–407: de Brecht 2013を引用し、準Polish空間をPolish空間とω連続domainの共通一般化として位置付ける導入。包含・特徴付けは章で外部理論として明示され、ここで新しい局所証明は提示しない。
- **除外維持** — `statement` L503–511: de Brechtの同値特徴付け・閉包性を引用された外部理論として紹介し、ここでは同値の証明を展開していない。
- **除外維持** — `prose` L513–514: 外部de Brecht特徴付けに続く、可算積と一般化Π⁰₂部分空間に関する閉包性の概説。章のproof scopeで外部の分類理論と明示され、ここで局所証明を提示していない。
- **除外維持** — `prose` L516–518: 外部の準Polish分類・閉包定理から得る包含例の一覧。Polish空間・ω連続dcpo・一般化Π⁰₂部分空間の一般的な分類は引用理論として扱い、具体的なinterval domainのω連続性・Scott区間の反例は別の局所主張として証明している。
- **除外維持** — `prose` L520–520: 直前の外部分類理論を要約する比較表の導入。表のdiscreteは前文にある特殊化順序を指す概略で、新しい圏同値や計算可能な翻訳の定理を提示しない。
- **除外維持** — `prose` L528–530: 一般化Borel階層とHausdorff–Kuratowski差階層定理の拡張をde Brecht 2013へ明示的に帰属させる外部理論の説明。直後のCantor部分空間に関する局所反例はこの除外から切り離し、通常本文として形式化済み。
- **除外維持** — `statement` L542–546: admissible domain representationの存在をSchröder・de Brechtの外部結果として引用。後続の基底補間などの局所補題は別途対象である。
- **除外維持** — `prose` L548–554: Schröder 2002とde Brecht 2013からの外部表現定理の出典を示す一文のみ。具体的な基底鎖による表現構成・名前域・admissibilityは後続の局所証明として別途監査する。

### tripos-topos-forcing-realizability

- **除外維持** — `prose` L8–11: forcingの条件とrealizabilityのプログラム添字を比較する章の動機付け。証拠の変換という読み方を紹介し、新しい定理・具体的言語の意味論・相互翻訳は定義していない。論理演算の具体的なlambda構成は後段の別単位として対応させる。
- **除外維持** — `prose` L13–18: 前章と付録のforcingを振り返り、triposと一般tripos-to-topos構成の位置付けを予告する導入。一般構成の定理は同じ導入のproof scopeで外部結果と明示され、具体的なlocalic/Kleene triposとPERの計算は別途監査する。
- **除外維持** — `prose` L20–24: 自然数添字と任意の無限TTE名を区別し、計算可能点のassemblyへの翻訳を次章へ送る導入。新しい局所翻訳の証明をここで提示せず、参照先inside-effective-topos章の構成はその章で別途監査対象とする。全ての外部点を含む表現空間とeffective toposの対象を同一視しないという対象範囲の説明である。
- **除外維持** — `prose` L26–31: effective topos・lightface点集合・TTE実現子を無条件に同一視しないという用語と対象範囲の説明。具体的な計算可能点翻訳はinside-effective-topos章へ明示的に送っており、ここで新しい同値や反例の局所証明を提示していない。
- **除外維持** — `prose` L38–42: U-smallな集合の圏という宇宙規約、一般定義を置く付録、Hyland/van Oostenの標準参照を案内する段落。具体的PER categoryとtoposの局所構造は後続の対応済み命題で扱い、一般tripos-to-topos同定をこの段落で証明したとはしない。
- **除外維持** — `prose` L44–47: 一般Hyland–Johnstone–Pitts tripos-to-topos定理を外部結果とし、局所的な述語・PER計算を本章の証明対象にするproof scopeの説明。除外の宣言自体を局所主張の省略理由には使わず、localic構成とrealizabilityの述語定義・演算は除外を解除して形式化へ接続した。
- **除外維持** — `prose` L53–60: 必要なlambda添字・PCA・assembly・圏論・forcingの参照節と読む順序、任意の発展項目、学習目標を示す読書案内。ここに独立した局所定理や構成はない。
- **除外維持** — `prose` L72–76: 一般tripos/PER構成の定義を付録へ送り、本章のforcingと自然数実現子の例を予告するroadmap。具体的なSetTriposとfunctional relationの構成は本章の個別箇所で監査し、一般定理は引用された外部理論として区別する。
- **除外維持** — `prose` L78–82: Kleene述語、PER category、有限極限、classifier、exponentialをどの節で構成するかを示す案内。構造の数学的主張は案内先の個別命題・証明で対応させ、ここに別の局所証明はない。
- **除外維持** — `prose` L88–88: 比較表の直前の「This single construction covers two different notions of evidence:」という導入文のみ。対応表はforcingとrealizabilityの概念的な対比として読んでおり、新しい圏同値やプログラムへの翻訳は主張しない。
- **除外維持** — `prose` L98–101: 直前の表を構造上の類比として読むよう注意し、条件とプログラム、generic filterと添字を同一視しないという比較の範囲を説明する段落。具体的な述語変換と論理演算は別途構成し、一般のtripos-to-topos理論は外部参照として扱う。
- **除外維持** — `prose` L129–132: localic triposから対応するlocalic toposへの一般同定をvan Oosten Ch.2に明示的に帰属させる一文。直前の点ごとのHeyting代数・再索引・ファイバー量化子・両随伴・両Beck–Chevalley・恒等普遍述語による具体的なSetTripos構成は除外を解除し、LocalicTripos.leanへ接続した。一般的なtripos-to-topos同定のLean証明があるとは扱わない。
- **除外維持** — `prose` L347–351: generic評価を、generic対象を選ぶ前の真理値と選んだ後の通常の真理という言葉で説明する解釈上の案内。M[G]での真理とfilter所属の同値や、非原子的完備Boole代数の完全素フィルター不存在の証明はそれぞれ別単位で扱い、この段落で新たな真理補題や圏同値を主張しない。
- **除外維持** — `prose` L353–356: 既出のforcingとlocalic triposを概念的に対比する説明。dense-set議論とnull-set回避の新しい翻訳をここで構成せず、各forcing章の計算と本節のBoolean真理値・generic評価の局所証明を別途対象に残す。
- **除外維持** — `prose` L358–362: localicな論理と計算的な証拠による論理の位置付けを述べるsurvey。一般sheaf toposの直観主義性とdouble-negation sheavesのBooleanizationは、この章の局所PER計算に使用する補題ではなく、Hyland/van Oostenを参照する標準的な一般topos背景である。ここで一般sheaf分類定理の証明を展開していない。realizabilityの具体的な論理演算と排中律の障害は別の局所箇所で形式化し、Booleanの排中律恒等式も別途接続した。
- **除外維持** — `prose` L1287–1289: 具体的な構成が一般tripos-to-topos定理の例であることをvan Oosten Ch.2へ明示的に帰属させる参照文。一般定理の局所証明ではなく、具体的categoryの有限極限・classifier・exponentialは直前までの別命題で形式化されている。
- **除外維持** — `prose` L1297–1300: internal logicの一般的な用語と、forcingとrealizabilityを比較する目的を説明する導入。新しい第一階構文の解釈やtoposを構成しない。Boolean排中律、generic評価およびrealizabilityの停止問題による障害は個別の局所箇所で扱う。
- **除外維持** — `prose` L1310–1315: 一般locale上のsheaf意味論とdouble-negation Booleanizationの標準的な背景説明。具体的な位相空間での反例や新しいsheaf構成・証明をここで提示せず、後続のPER/実現可能性の局所証明に依存する補題でもない。一般topos理論のsurveyとして対象外とし、直後のlambda実現子と停止問題の具体的議論は除外を解除して独立に形式化へ接続済み。
- **除外維持** — `prose` L1323–1324: 直後の概念比較表を導入する「The comparison is:」という案内文のみ。Booleanizationや排中律についての数学的主張は周囲の各段落を独立に監査し、このラベルの除外に巻き込まない。
- **除外維持** — `prose` L1332–1334: forcingを宇宙の変化、realizabilityを計算可能な証拠という観点で読むという章末の解釈上の案内。新しい不変性定理や実現可能性の同値の証明を提示していない。

### inside-effective-topos

- **除外維持** — `prose` L8–12: 章全体の構成を振り返るsynthesis。計算可能点assemblyによる翻訳と、自然数添字と任意の外部名を区別するという対象範囲を要約する。具体的な翻訳・積・関数対象・選択不能性は本文の別単位で対応させている。
- **除外維持** — `prose` L14–17: 内部数学の成功・失敗を計算的証拠の観点から読むという動機付け。ここで内部妥当性と外部証明の使用公理について新しい形式的な必要十分条件を提示していない。実際の排中律・比較・零点選択の障害は個別定理として別途監査する。
- **除外維持** — `prose` L23–26: 前章を振り返り、この章が全ての外部点ではなく計算可能点assemblyを使うことを宣言する導入。assemblyと計算可能点の定義・写像は後段で具体的に構成されており、ここに別の局所定理はない。
- **除外維持** — `prose` L28–31: 計算可能点、積、関数対象、内部原理、名前とtrackerによる零点選択という読む順序の案内。二つの入力表現の差は、別々の局所構成・不能性定理で確認する。
- **除外維持** — `prose` L33–39: 対象範囲の明示。Churchのテーゼ・Markov原理・KLS/Ceitinに基づく内部連続性の実現可能性妥当性をHyland/van Oostenの標準K1意味論から輸入すると明記する。局所的なassembly/TTE翻訳や演算までこの宣言で除外せず、個別に形式化へ接続する。
- **除外維持** — `prose` L45–52: 前提となるtripos・assembly・圏論・TTE・領域理論の節と学習目標を示す読書案内。新しい数学的構成や局所証明を提示していない。
- **除外維持** — `prose` L178–181: 外部の全ての枝と、実現子をもつ再帰的な枝を同一視しないためのrecursive-treeの警告。特定の木の構成・再帰性・無限枝・再帰的枝不存在の証明は提示せず、標準的な背景例として可能性を挙げている。この木を後続のassembly翻訳や零点選択の局所証明に使用していないため、具体的な非閉性の証明対象とは扱わない。Leanでそのような木を構成済みという判定ではなく、外部/内部の解釈範囲の説明として除外を維持する。
- **除外維持** — `prose` L293–297: 位相の外部理論と、計算に使う際に追加する証拠の区別を説明する読み方。全ての開集合が半決定可能と誤読されないよう、所属を計算で扱うには名前上の半決定手続きを供給する、という条件付きの文へ日英で修正した。既存LambdaSierpinski.SemidecidableFromNamesがその条件を定義する。選択や関数のtrackerについて新しい一律の存在定理を主張する箇所ではない。
- **除外維持** — `prose` L494–496: internal logicを直観主義高階論理として読む標準的な意味論上の案内。新しい論理体系の完全な構文・健全性証明をここで構成しない。直後の具体的な実現子の各節は、この案内とは別の局所確認対象として保持する。
- **除外維持** — `prose` L505–506: 次の三つの内部原理を導入する接続文。各原理の正確なK1意味論での妥当性は、章のproof scopeで標準参照からの外部入力と明示されている。
- **除外維持** — `statement` L513–520: 内部Churchのテーゼは章の範囲指定でK1実現可能性の外部結果として輸入し、内部意味論での証明をこの箇所には展開していない。
- **除外維持** — `prose` L522–525: 明示的に輸入された内部Churchのテーゼの読解であり、内部Baire関数対象と外部の全ての無限列を同一視しないための説明。ここで新しい名前から添字への一般的な計算可能変換を構成していない。
- **除外維持** — `statement` L527–535: 内部Markov原理は明示的に引用するK1の結果。非有界探索という実現子の説明はあるが、内部述語の意味論と一様実現子の構成・検証はこの箇所では概要に留まる。
- **除外維持** — `prose` L537–538: 外部K1意味論から輸入されたMarkov原理の計算的な読み方。非有界探索と二重否定が担う役割の概説であり、この箇所で任意の内部述語の意味論と一様なlambda実現子を新たに定義・検証する局所証明ではない。
- **除外維持** — `statement` L540–547: 内部連続性はKLS/Ceitinの実効的作用素定理を実質的な外部入力と明示し、TTEの有限使用原理と区別している。その外部定理の再証明は要求しない。
- **除外維持** — `prose` L549–553: KLS/Ceitinの実効的作用素定理を実質的な外部入力と明記して帰属させる説明。自然数添字上の外延的操作を、TTEの単純な有限照会原理へ置き換えて証明済みとはしない。
- **除外維持** — `prose` L615–616: 一般のelementary toposで完全な選択公理が排中律を含意するというDiaconescuの外部定理を明示して用いる箇所。その一般定理をここで再証明せず、前提となる本モデルの排中律の障害は別の局所証明として形式化する。
- **除外維持** — `prose` L862–865: TTEから計算可能点assemblyへの移送をどう読むか、逆方向を無条件に仮定しないというconstructive-analysisの案内。具体的な新しい逆変換や非存在定理をこの段落で提示していない。
- **除外維持** — `prose` L867–869: 既に構成した実数加法を、名前変換・添字変換・assembly写像という三つのレベルで振り返る参照文。局所計算は参照先の積・加法の命題と証明で形式化されている。
- **除外維持** — `prose` L871–873: 指定した関数assemblyと入力のpromiseに対する既存の添字零点選択不能性定理を読むための案内。対象やpromiseを省略した、より広い内部関数空間への新しい一般化は主張しない。
- **除外維持** — `prose` L879–887: Lawvere--Tierney局所作用素，subtoposおよび相対実現可能性に関する引用されたモデル・分離結果の紹介であり，固定assemblyの局所証明とは区別する。
- **除外維持** — `prose` L889–895: Lawvere--Tierney局所作用素，subtoposおよび相対実現可能性に関する引用されたモデル・分離結果の紹介であり，固定assemblyの局所証明とは区別する。

### outlook

- **除外維持** — `prose` L3–8: 全体の導入的総括で、共通の空間と用語を列挙する。新しい構成・補題・証明を提示しない。
- **除外維持** — `prose` L12–18: 既存章の対象を比較する概説。測度・forcing・represented space・軌道関係の新しい構成や証明はここでは行わない。
- **除外維持** — `prose` L20–22: Polish空間を共通基盤とする意義の説明で、特定の閉包定理や絶対性命題をここで主張・証明しない。
- **除外維持** — `prose` L26–26: 後続のforcingとrealizabilityの比較への導入文。数学的な局所補題を含まない。
- **除外維持** — `prose` L28–36: forcingとeffective toposの既存章への振り返り。computable-point assemblyはinside-effective-topos章を明示し、内部原理も指定対象に限定した背景説明。ここで内部原理や独立性を新しく証明する箇所ではない。
- **除外維持** — `prose` L38–41: 外部の提示と内部の数学を比較する解釈上の総括。新たな翻訳写像や同値定理は構成しない。
- **除外維持** — `prose` L45–47: 古典的DSTと分類問題の研究対象を比較する動機説明。具体的な同値関係について還元を構成しない。
- **除外維持** — `prose` L49–52: Kechris1999を明示した研究史とBorel還元の読み方の説明。局所的な分類定理・非分類定理の証明ではない。
- **除外維持** — `prose` L56–57: 現代DSTの研究プログラムを列挙するための文献概説の導入。
- **除外維持** — `prose` L59–62: Becker–Kechris、Becker、Hjorth、Gaoの文献案内と既存2節への道案内。新規の群作用・turbulence証明なし。
- **除外維持** — `prose` L64–69: Jackson–Kechris–Louveau、Kechris–Miller、Hjorthの研究プログラムの紹介。可算Borel関係の性質を局所的に証明・使用する補題ではない。
- **除外維持** — `prose` L71–75: 記述的グラフ組合せ論の文献案内。彩色等の存在をこの章で構成・証明しない。
- **除外維持** — `prose` L77–83: effective・quasi-Polish・generalized DSTの文献概説。引用した研究結果の証明を本章で展開しない。
- **除外維持** — `prose` L87–88: 演算子環とDSTの歴史的関係の導入。形式化対象となる局所構成を含まない。
- **除外維持** — `prose` L90–92: 演算子環の証明を専門文献に委ねるsurvey bridgeであることを明示する範囲宣言。
- **除外維持** — `prose` L94–102: Sabok2016による核型C*環同型の普遍性を引用し、Elliott不変量のBorel性の必要性を解説する外部分類結果の概説。具体的還元や不変量写像の局所構成なし。
- **除外維持** — `prose` L104–109: II1因子はSasyk–Tornquist2009、Banach空間はFerenczi–Louveau–Rosendal2009の外部非分類・完全性結果を引用する。局所証明なし。
- **除外維持** — `prose` L111–118: Glimm–EffrosとEffrosの歴史およびC*環への元来の適用を解説する。既存節への参照であり、type-I分類や表現空間の構成を本章で証明しない。
- **除外維持** — `prose` L120–125: 決定性と正則性の既存節を参照する背景説明。軌道のBorel性は群作用章の既存結果の再述で、新規のゲーム・正則性証明はない。
- **除外維持** — `prose` L127–128: Farah2019とKechris–Miller2004への読書案内のみ。
- **除外維持** — `prose` L132–137: 各Partの前提関係と読む経路の説明。新規定理ではない。
- **除外維持** — `prose` L139–166: 既に扱った各部の道具と結論を比較する展望表であり，独立した新規証明ではない。
- **除外維持** — `prose` L168–173: 案内表を読み解く本書の構成の総括。列挙した道具の数学的証明は各既存章の対象。
- **除外維持** — `prose` L175–177: Baire・Cantor・実数・standard Borel空間の役割を再述する総括。ここで普遍性の追加構成はない。
- **除外維持** — `prose` L181–185: 定義可能性・generic性・計算可能性を区別し、付録へ案内する結語。選択関数等の具体的な存在定理は提示しない。

### appendix-metric-spaces

- **除外維持** — `prose` L3–11: 付録の内容とChoquet metrizationへの用途を案内する導入文。新たな数学的主張・証明はない。
- **除外維持** — `prose` L15–19: 位相と開閉集合の標準定義。新しい証明を伴わずmathlibのTopologicalSpaceを前提に使う用語の説明。
- **除外維持** — `prose` L21–24: 近傍と位相基底の標準定義および標準の局所基底条件の説明。新しい空間・写像の構成はなく基礎用語の導入。
- **除外維持** — `prose` L26–27: 稠密部分集合と可分性の標準定義。局所的な稠密集合の構成・可算性証明を含まない。
- **除外維持** — `prose` L29–31: 列の収束の標準定義。ここで新たな収束結果を証明しない。
- **除外維持** — `prose` L35–44: 距離・球・距離位相・compatible metric・metrizableの標準定義。具体的な距離の構成や互換性の証明を含まない。
- **除外維持** — `prose` L46–52: Cauchy列・完備距離・完全距離化可能性の標準定義と両者の区別。具体的な完備性証明・反例の構成を含まない。
- **除外維持** — `prose` L73–80: 近傍基・第一可算・第二可算の定義だけを記載する。可分性との同値，部分空間，列閉性，連続性判定は直後の四つのLean対応済み主張に分離されている。
- **除外維持** — `prose` L206–214: この節で証明する零次元の場合と一般論の文献を案内する範囲宣言。一般次元の比較定理を証明する箇所ではない。
- **除外維持** — `prose` L228–237: 境界の部分空間位相と整数添字による再帰の読解指示。一般次元のwell-definednessと位相不変性はEngelking1978 Sections 1.1/1.6を明示して引用する外部背景であり局所証明ではない。

### appendix-logic

- **除外維持** — `prose` L3–12: 付録の目的と、古典的意味論と内部論理の取り扱いの違いを案内する導入文。新規の論理体系や翻訳を構成する段落ではない。
- **除外維持** — `prose` L14–23: 構文・証明体系・完全性・モデル理論・不完全性・定義拡張への節案内。各局所証明は参照先で別途対象となる。
- **除外維持** — `prose` L104–113: 完全な括弧付き構文と、通常の文章での括弧省略に関する表記規約。新規の構文解析器の正当性や一意性を証明する箇所ではない。
- **除外維持** — `prose` L388–394: φ(x)とφ(t)の用法を定める略記規約。代入そのものの定義・正当性は別途接続済みの対象で、この一文に新規の主張はない。
- **除外維持** — `prose` L420–425: 後続の自然演繹規則表の見出しのみ。各規則を定める数式は個別にDerivesへ接続する。
- **除外維持** — `prose` L466–475: 古典的体系からLEMを除く直観主義的変種の背景説明で、ここではその体系の健全性・完全性を証明しないと明示する。内部意味論の実際の展開先をcat-internal-logicとrealizability-triposに指定する読書案内。古典的Derivesを直観主義の実装と扱わない。
- **除外維持** — `prose` L714–719: 直後の代入補題を紹介する一文のみ。補題の主張・証明は別の対象として保持している。
- **除外維持** — `prose` L1327–1334: 直前のLöwenheim–Skolemの結果からinternal-model-closure節へ案内する説明文。ここで新しいcountable-transitive-modelの存在を主張・証明する箇所ではない。
- **除外維持** — `prose` L1364–1372: Zach2025を明示して引用する算術化・Qでのnumeralwise representabilityおよび固定numeral以下の有限性・比較の外部入力。Q内部の証明をこの段落で展開しない。これらの入力を使う後続の具体的な算術文と対角探索の局所構成は別単位で対象に残す。
- **除外維持** — `prose` L1374–1378: 引用した標準の有限証明符号化・実効的構文操作を対角探索の入力として説明する。有限証明証明書のtotal lambda checkerとc.e.公理集合のmembership判定可能性を区別し、外部のproof-coding theoremと後続の具体的な対角探索を分けて扱う。
- **除外維持** — `prose` L1463–1468: 定義拡張の議論で理論Tと言語Lを固定する設定文のみ。新しい主張・構成・仮定の充足証明は含まない。
- **除外維持** — `prose` L1472–1481: 有限の変数・項・量化子列をvecで表すメタ言語の略記規約。新しい項形成操作ではないことを明示する。実際の同時代入は次の補題として別途対象。

### appendix-set-theory

- **除外維持** — `prose` L3–11: 付録の内容・論理付録との関係と標準参考文献を案内する導入文。個別の数学的主張は後続の構成・補題として対象に残す。
- **除外維持** — `prose` L13–22: 後続のforcing・Borel-code・measure・random forcing付録への依存関係を案内する文。新規の模型・構成をここでは主張しない。
- **除外維持** — `prose` L27–35: 直後の公理リストと後続の略記の定義への案内。各公理と略記は別の本文単位として対象に残す。
- **除外維持** — `prose` L176–183: 本文で関数をgraph/domain/codomainの組として呼ぶ場合と、ZFCが構成するgraphとの表記上の慣例の説明。ここで新しい関数対象や同値定理を構成する箇所ではない。
- **除外維持** — `prose` L185–193: ZFとZFCの命名規約と本書でACを使う場面の列挙。Tychonoff・cardinality・successor-cardinal regularityの証明をこの段落で展開せず、ここで新しい局所補題として使用しない背景説明。
- **除外維持** — `prose` L394–404: 外部の表現定理と、内部の順序数・graphを得るための追加の閉包仮定を区別する読書案内。internal_ordinal_representationがtransitivity・Pairing・Separation・Replacement・internal minimaを明示してモデル内のα,Fを構成することを確認した。この段落自体は閉包の反例や新たな表現定理を証明せず、認識・制限・内部Hartogsの議論を明示的に後の節へ委ねているため対象外。後節の実際の構成と証明をこの判定に含めない。
- **除外維持** — `prose` L598–608: 圏論付録で固定するGrothendieck宇宙という追加仮定と、この節の役割を案内する導入。宇宙の存在や新たな閉包・濃度命題をこの段落で証明せず、具体的な定義と宇宙定理を後続段落で扱う。ZFCに対する仮定の強さの位置付けは背景説明として対象外にし、後続のstrong limit・到達不能性・閉包例・宇宙公理の同値性はこの判定に含めない。
- **除外維持** — `prose` L721–734: 固定Uの下でset・small・SetCatをどう読むかを宣言し、実現可能性の具体的構成を圏論付録へ委ねる規約。再読して、omega_memという前提と、SetTheoryCategorySizeでグラフ・始域・終域を持つ関数集合および実際の関係同値類がU内に属する証明を確認した。LeanのTypeレベルを固定ZFSet宇宙への所属と同一視していない。ここでは新たな局所的構成をせず、委ね先の本文とサイズ証明は別に接続する。
- **除外維持** — `prose` L981–986: 直後のInj/Surj/Bijの定義を導入する一行の見出し。数学的内容は次の独立した表示式の単位へ接続し、この案内文だけを対象外とする。
- **除外維持** — `prose` L1074–1080: 絶対性の階層が後続の強制法・独立性・無矛盾性の節で担う役割を説明する結びと参照。ここで独立した定理や新しい証明を展開しない。

### appendix-internal-models

- **除外維持** — `prose` L3–9: 本付録がforcingとは独立に推移的モデル内の構成を展開し、forcing付録の前提を供給するという導入。新しい局所定理を主張しない。
- **除外維持** — `prose` L11–22: 三つの節の内容と依存関係を案内する段落。具体的な閉包、再帰、rank、Collection、ChoiceとHartogsは各節の定理・証明として対象に残す。
- **除外維持** — `prose` L119–128: 直前の内部image定理の適用条件を読み直す注意。valuesの内部所属と内部式によるgraphの定義が必要であることを明記し、後の具体的name構成へ先送りする。この注意自体は任意の外部構成がモデル内に入らないことの独立した反例を構成しない。
- **除外維持** — `prose` L185–194: 部分的再帰assignmentを一つの内部setとして扱えるための既証明の前提と、後の内部再帰定理で示すべきことを区別する読書案内。任意の外部assignmentの非内部性を新しい局所定理として証明する箇所ではない。
- **除外維持** — `prose` L606–614: 既存の内部membership再帰をrank・累積段階・fixed point・Collectionへ使う、後続節の依存関係の案内。各後続定理の証明とChoice不使用の確認は別単位として保持する。

### appendix-forcing

- **除外維持** — `prose` L3–11: 本付録がPolish空間上のgeneric pointsの背後にある集合論的forcingを扱うという導入。新しい個別の数学的主張を証明する段落ではない。
- **除外維持** — `prose` L13–25: 集合論付録・主章・本付録の役割と収録内容を案内する序文。定義可能性と真理補題を主章の正当化として使う依存関係の説明であり、実際のforcing構成と証明は後続の独立単位として対象に残す。
- **除外維持** — `prose` L29–36: 内部モデル付録への参照と、各構成に必要な有限fragmentを満たす推移的基礎モデルを固定するという仮定の宣言。ここで基礎モデルの新たな存在定理を主張しない。
- **除外維持** — `prose` L44–50: 直後のdense/open dense/predenseの三つの定義を導入する見出しだけの行。各定義は標準IsCoinitial・IsLowerSet・共通強化の存在へ接続し、この案内行だけを対象外とする。
- **除外維持** — `prose` L93–102: Rasiowa–Sikorski構成が外部で行われること、filterのモデル内所属をこの構成から主張しないことと、Baire-categoryの構成との類比を説明する背景。trivial forcingの場合との対比も例示で、この段落で非内部性の反例や新しいgeneric存在定理を証明しない。
- **除外維持** — `prose` L106–113: 名前による拡大の定義へ移るための説明。Gを加えて何らかの閉包を取る手続きとの不一致を数学的反例や独立定理として証明する箇所ではなく、次の実際の名前・valuationの定義が対象となる。
- **除外維持** — `prose` L193–201: これからcheck-nameの公理を保ってP,Aをパラメータに固定し、内部relationを用いる構成を行うという導入。具体的なdecision relationと名前の内部所属は直後の定理と証明で別に扱う。
- **除外維持** — `prose` L799–809: fixed formulaごとのforcingTranslationと、構文的forcingからsemantic forcingへの適用条件の違いを説明する注意。任意のformula code用の単一の内部truth predicateをここでは主張していないという範囲の宣言であり、Tarskiの非定義可能性を証明したとみなす判定ではない。内部test setsと真理補題の実際の構成は後続の定理で対象に残す。
- **除外維持** — `prose` L813–823: 次の節で四つのdense testを共通の定義可能性からM内に置くこと、P,Rをパラメータとして保つことを案内する段落。membershipTest_mem・equalityTest_mem・implicationTest_mem・universalTest_memからmodelGeneric_meets_testsへ至る個別の構成と証明は別単位として対象に残す。
- **除外維持** — `prose` L1109–1117: 直後のdense forcingのworking principleを導入し、Polish空間の応用での役割を説明する案内。working principleそのものはmodelGeneric_truth_of_dense_semantic_forcingへ接続し、この導入だけを対象外とする。
- **除外維持** — `prose` L1122–1128: 直前の、各条件の下にforcing条件を得ればgeneric拡大で真になるという補題をdense-set argumentと呼ぶ一行の説明。新しい局所主張ではない。

### appendix-borel-absoluteness

- **除外維持** — `prose` L3–15: 付録全体の内容と、内部評価・rational measure bounds・finite-test coding・包含移送・次のmeasure付録との依存関係を案内する導入。個々の構成と証明は後続の独立単位として対象に残す。
- **除外維持** — `prose` L385–392: 次のrational measure boundsからranked counterexample treesへ進む節順の説明。数値比較やtree inclusionの具体的な定理はそれぞれのstatement/proof単位として対象に残す。
- **除外維持** — `prose` L505–515: 次のcounterexample tree構成の入力であるvalid expression・標準cylinder basis・B_cという記号と前提を固定する導入。lambda programによるlabel計算を仮定しないこの集合論的構成の範囲を宣言している。実際の有限row tests・tree・branch criterionは直後の構成と証明で扱い、この案内文を新たな計算可能性定理とはしない。
- **除外維持** — `prose` L599–608: 外部のrank criterionと、内部tree/rankを構成する義務を区別し、次節のrecognition・transferへ進む案内。criterionだけから内部所属を推論できるという主張を避ける注意であり、非内部rankの反例や新たな存在定理をここで証明しない。
- **除外維持** — `prose` L707–714: 与えられた内部rankの認識・移送から、subset minimaを用いたrank存在の構成へ進む案内。存在とChoiceの用途は直後の定理の仮定・証明として別に対象に残す。
- **除外維持** — `prose` L817–824: 次の節で、内部branchがないことからcoded treeのsubset-minimum assertionを導くという予告。具体的なminima導出と内部rankの構成は後続の定理・証明として対象に残す。
- **除外維持** — `prose` L964–972: counterexample-treeのために次の内部算術・list coding・finite testsを準備するという構成順の案内。各graphの内部所属やlambda計算との対応は後続の実際の構成・定理で扱う。
- **除外維持** — `prose` L1085–1092: 既に構成した算術graphから、同じlambda番号付けを用いるlist encoding/decodingの内部graphへ進むという案内。新しい番号付けや別の計算モデルを導入する主張ではなく、実際のgraph構成は次の定理として対象に残す。
- **除外維持** — `prose` L1201–1208: 算術・list graphsを使う有限テストの一様解釈原理を導入する案内。共通のbounded-predicate compilerの意味保存・Delta0性・graph collectionは次の独立単位で対象に残す。
- **除外維持** — `prose` L1244–1254: 内部subsetを得る一般的補題の適用には有界記述・内部パラメータが必要であり、外部regularityから得たclosed approximationだけでtree codeの内部所属を結論しないという注意。この段落で新たな反例やinternal approximation存在を証明せず、その具体的な構成は後のmeasure付録に残す。
- **除外維持** — `prose` L1416–1427: 後続のclosed-inclusion transferのために、モデル公理、標準cylinder basis、valid label graph、内部tree-node set、外部/内部解釈の記号を固定する文脈設定。実際の包含移送は直後の定理・証明として対象に残し、この仮定の宣言だけを対象外とする。

### appendix-measure-absoluteness

- **除外維持** — `prose` L3–11: 付録の目的と構成順序の導入。個々の測度値構成・比較定理は後続で別に対応し、この段落で新たな局所証明を提示していない。
- **除外維持** — `prose` L13–19: 後続のrandom forcing付録と本文章への案内。ここに独立した測度代数・名前評価・generic回復の定理を追加したとは扱わない。
- **除外維持** — `prose` L218–228: 収束からの段階選択はexists_internal_openCode_approximationの存在証明であり、計算可能な収束率を主張しないという注意と後続構成への案内。新たな計算可能性定理を提示していない。
- **除外維持** — `prose` L230–239: 可算族では全グラフの内部所属が必要という適用条件とモデル公理の再掲。直後のinternal_definable_choiceの前提を説明する導入で、内部所属の反例を証明する段落ではない。
- **除外維持** — `prose` L331–345: 近似のadmissibility、子族のグラフ、有限tail評価、実数コード、測度との一致を扱う後続節の参照一覧。各構成は参照先の対応対象で、このロードマップを追加の証明としない。
- **除外維持** — `prose` L476–484: 直前の内部totality補題を可算選択へ適用する案内。全入力グラフが内部にあることを改めて要求しており、外部の点ごとの選択から内部列を得る追加原理を主張しない。
- **除外維持** — `prose` L486–495: 全ノードの内部解釈族を扱うための入力公理・パラメータとB_sの局所記号を導入する文。実際の族構成は直後のinternalInterpretationFamily_memで別に対応済み。
- **除外維持** — `prose` L552–561: 既に証明した内部totality、全族選択、admissibilityの各定理を適用する順序と、計算可能な選択ではないという注意。新しい選択原理を追加していない。
- **除外維持** — `prose` L921–931: 測度定理を内部で適用する際には全列グラフを入力にするという前提と、モデル公理・木の設定。内部clopen列の実構成は後続定理で対応済みで、新たな反例は述べていない。
- **除外維持** — `prose` L992–998: 構成済みの全clopen列を連続性の定理に渡す順序と、先に数値code演算を用意するという読み方の案内。
- **除外維持** — `prose` L1000–1008: 外部測度から作ったcodeと、内部で認識したcodeの外部decodingとを比較する動機付け。必要な逆方向の実定理は直後のcut条件・decodingで別に対応。
- **除外維持** — `prose` L1081–1088: 直前のdecodingと順序定理の利用の説明、および加法と下限の構成へ進む案内。独立した新定理は提示していない。
- **除外維持** — `prose` L1242–1248: 加法と可算下限の定理を有限加法性・連続性に使う旨の節案内。数値演算の定理そのものは既に別に対応。
- **除外維持** — `prose` L1442–1450: 連続性を適用する対象が内部の全列であるという範囲の注意と次節の案内。old points上の外部可算加法性を主張したり、その反例を証明したりする箇所ではない。
- **除外維持** — `prose` L1452–1460: 有限測度graphの記号、モデル公理、可算加法性を内部全列だけに適用する条件の再掲。実際の列演算は続く定理で別に対応。
- **除外維持** — `prose` L1582–1588: 閉集合での値と近似定理を次節の一般Borel同定へ使う旨の案内。
- **除外維持** — `prose` L1592–1602: 同定定理に使うモデル・measure graph・正規化の前提と点の表記を固定する導入。可算加法性を閉集合値の同定で使うという証明依存関係の説明で、新しいmeasure存在定理ではない。

### appendix-random-forcing

- **除外維持** — `prose` L3–10: random forcing付録が使う測度絶対性とforcing基礎を明示する導入。具体的な構成は後続の各定理で別に対応済み。
- **除外維持** — `prose` L12–20: 内部商・random-real名・Borel真理・点からのgeneric回復を辿る章構成の案内。各結果をここで追加に証明する箇所ではない。
- **除外維持** — `prose` L26–35: 全商写像を先に内部構成する理由と、有限測度則と可算加法性の依存関係の説明。relationClassMap_mem、randomRealName_memは有限測度則のみを用い、外部Borel測度との同定は後続比較定理を使う。
- **除外維持** — `prose` L37–44: 一般の内部商構成に使うモデル公理・同値関係の仮定を固定する文。商の実定義は直後のrelationClass/relationClassMap/relationQuotientへ対応済み。
- **除外維持** — `prose` L111–120: 内部測度域の集合の商と、全外部Borel集合の測度代数を区別する適用上の注意。商の構成だけから比較写像やold points上の外部測度を得たとは主張しない。
- **除外維持** — `prose` L122–131: random-real名の構成に使うInfinity、公平なcylinder値、null関係・商写像・正条件の記号を固定する仮定。bit cellの値と全判定表は後続で構成され、ここで仮定を証明済みの結果に変えない。
- **除外維持** — `prose` L207–218: 比較定理に引き継ぐモデル公理、内部可算加法性、cylinder正規化と近似クラスの設定。比較写像の構成は後続定理で別に対応済み。
- **除外維持** — `prose` L593–603: forcing notionを符号化したPと順序関係、必要なモデル公理を固定する文と、Gに依存しない名前をこれから作るという案内。実定義separatedName/powerSetName/functionSpaceName/borelInterpretationNameはいずれもGを入力に持たず、値の同定は後続定理で別に対応。
- **除外維持** — `prose` L690–698: 内部random orderとmeasure graphを引き継ぎ、Y_Mと測度域の包含条件を仮定する導入。負のdecisionを有限加法性から得る実証明は直後の補題で対応済み。
- **除外維持** — `prose` L814–826: 全内部Borel解釈を測度域Dとするこの節の設定とA_cの表記。LeanのHasInternalBorelRepresentativesと全内部code解釈のdomain所属hcodeが両方向の要求を保持し、これを有限測度則から導いたとは扱わない。
- **除外維持** — `prose` L914–923: dense集合からのconull coverと全符号列が必要になる理由の説明。外部可算性だけから内部列所属を結論しないという注意で、コード選択の実証明は後続のinternal_borel_code_sequenceが与える。
- **除外維持** — `prose` L925–932: 有限cover補題に使う測度域・value graph・ambient Yと族Eの前提、および次に扱う構成の案内。
- **除外維持** — `prose` L1064–1072: 直前に得た全内部集合列を、後続の内部Borel code選択へ渡す順序の案内。全code候補集合を先に構成する必要を説明する文で、新しい選択原理を仮定していない。
- **除外維持** — `prose` L1076–1085: 内部representative選択の目的、モデル公理、既出の有限語グラフ・即時拡大関係、全label graphの型を固定する設定。実際の局所規則はlocalShapePredicate、全valid code集合はinternalValidCodes_memへ別に対応済み。
- **除外維持** — `prose` L1150–1159: モデル仮定と内部Cantor space・全valid code集合・canonical basisを固定する前提。これらの所属は先行するinternalCantor_mem/internalValidCodes_mem/canonicalBasisWordGraph_memを利用し、新しい構成を主張しない。
- **除外維持** — `prose` L1224–1230: 最終genericity定理へ引き継ぐmeasure比較、内部可算加法性、Choiceを含むモデル公理の前提の再掲。

### appendix-lambda-calculus-computability

- **除外維持** — `prose` L3–17: 本全体で採用する計算概念・用語の規約とChurch–Turing thesisを区別する導入。数値出力の実際の意味はnumericalValue、有限arityの部分関数はComputesPartial/LambdaComputable、queryはOracleStepで定義し、他モデルとの同値を本書内の局所証明とは扱わない。
- **除外維持** — `prose` L19–28: 3つの計算付録の依存順序と内容への案内。個々のlambda構成は後続の対応対象で、ここで別のrealizerを追加したとは扱わない。
- **除外維持** — `prose` L30–38: Turing完全性という古典的な他モデル比較を踏まえた動機付け。比較の文献は同章のBarendregt/Sipserで指定され、本書のuniversal lambda評価や停止問題の実証明とは区別する。別の機械モデルへのsimulationを形式化済みとはしない。
- **除外維持** — `prose` L61–69: 印刷されたlambda式の省略記法と優先順位・結合規約。実際の構文はTermのvar/app/lamで明示し、パーサの正当性定理をこの記法の説明から要求しない。
- **除外維持** — `prose` L654–662: 有限データ用lambda項を構成する順序とType-Two利用節への案内。各閉項と有限β還元は後続の定理に別に対応。
- **除外維持** — `prose` L938–944: 既出の数値pairingを6×6格子に表示する図の座標と読み方。新しいpairingの定理ではなく、図の視覚的再審査はここでは行わない。
- **除外維持** — `prose` L946–970: 既出のNat.pairの2分岐式を格子の各点に記すTikZ描画指示。数値pairingの数学は先行定理で対応し、この図を新たな局所的証明と数えない。視覚的承認は別途とする。
- **除外維持** — `prose` L1070–1075: 次の有理数code定義に入る短い案内。符号付き分子と正分母の実定義とその被覆性は直後に別に対応。
- **除外維持** — `prose` L1367–1376: これまで構成した自然数・pair・有限list用の閉lambda項を計算概念の定義に使う旨の案内。一般の部分関数の定義は直後のComputesPartial/LambdaComputableで対応。
- **除外維持** — `prose` L1388–1396: Turing計算・partial recursive functionとの古典的比較の明示的な文献案内。この比較を局所形式化の証明対象に追加せず、本書のlambda項による計算の定義とは分離する。
- **除外維持** — `prose` L2545–2550: 次の3つの結果を利用する旨の導入ラベル。結果そのものは後続の対応対象。

### appendix-type-two-computation

- **除外維持** — `prose` L7–17: 3つのlambda付録の依存関係と、この付録で扱う構成の順序を示す案内。実際の閉項・beta/query導出・各部分定義域の主張は後続の定義と証明へ別に対応している。
- **除外維持** — `prose` L31–43: effective-dst節で導入した実数パラメータ付きpointclassの定義を再掲し、そのパラメータをlambdaプログラムの入力引数として読む旨の説明。この段落は新しい階層の正規形・普遍集合の証明を提示していない。ここで形式化したOracleStep/TuringReducibleと、参照先のpointclassの定義・外部の古典的記述集合論の結果とは区別する。
- **除外維持** — `prose` L47–55: 直後のInput-query computation and realizationの定義への導入。任意のpを許すOracleStepと、指定されたD上だけに計算を要求するTypeTwoComputesが本体で、この導入から別の有限記述やcomputable nameの仮定を加えない。
- **除外維持** — `prose` L669–677: 有限データ用の閉項を入力名上の操作へ拡張する構成順序の案内。各具体的なcomposition、pairing、tagging、searchの項と還元は後続の対応対象で、ここに新しい独立した構成はない。
- **除外維持** — `prose` L1159–1168: 成功時の値と失敗時の0を返す直前の有限trialを、既出のresult searchに渡す旨の参照案内。実際の値探索と無成功時の未定義性はresultSearchTerm_oracle_hit/no_output、入力名を保った全体の正確なdomainは後続の探索定理で扱っており、この案内を新たなrealizerの存在証明とは数えない。
- **除外維持** — `prose` L1535–1546: 次の有限syntax compilerで用いる閉項とnamed representativeをあらかじめ固定する前提・記法の設定。composeSyntax/pairSyntax/currySyntaxとCodeTransformの実際のコード生成を後続で対応し、代表元の選択を計算可能な無限選択や別言語のinterpreterとは扱わない。

### appendix-effective-computational-constructions

- **除外維持** — `prose` L3–13: この付録が先行する数値lambda構文とType-Two beta/query規則を再利用する旨の導入。後続の個別構成で実際の閉項・計算の仮定・保存するパラメータを別に確認し、この導入を新たな計算モデルや独立の存在定理とは数えない。
- **除外維持** — `prose` L15–23: 付録の構成順序と、応用先のeffective DSTおよびTTE章を示す案内。列挙された各構成の数学的・計算的主張は後続で別に対応する。
- **除外維持** — `prose` L1824–1833: 可算和constructorに必要な仮定の適用範囲を確認する説明。unionLabelProgram_computesは族全体のjoint label programを明示的に要求し、各添字の個別プログラムから一様な族を選択したとは扱わない。結論はラベルの計算だけで、well-foundednessの判定やvalid codeの選択は主張していない。
- **除外維持** — `prose` L2203–2212: 既出の有限tabulationプログラムを次のword pairingに使うという1文の参照案内。tabulation本体とそのbeta還元はlambda-finite-tabulationで別に対応しており、ここから新しい計算手続きの存在を追加したとは数えない。

### appendix-category-theory-realizability

- **除外維持** — `prose` L4–14: 付録の目的・依存関係・読者への導入で、新しい構成や証明を置く段落ではない。任意PCA上の個々の構成は後続の命題・証明で別に監査した。
- **除外維持** — `prose` L16–25: 四段階の章構成と参照先の案内。各節の実際の定義・構成・証明は別に接続し、この導入から一括して形式化済みとは扱わない。
- **除外維持** — `prose` L27–39: 具体的な有効トポスの読む順序とMac Lane、Mac Lane–Moerdijk、van Oostenへの文献案内。参照先の数学的主張は独立の監査対象であり、この案内には追加の局所的証明がない。
- **除外維持** — `prose` L181–189: 同値が構造を保存するという標準的な圏論の概説。章頭で参照するMac Laneの背景理論であり、この付録の局所的な構成の証明として提示されていない。具体的なPERとmodest assemblyの同値は別の定理と証明で接続済み。
- **除外維持** — `prose` L205–215: 自由・忘却、離散位相の例と随伴関手定理を紹介する標準背景。Mac Laneに委ねる一般理論で、付録でsolution-set theoremや局所可呈示性を構成・証明してはいない。局所的に必要なassembly exponentialの随伴は別に証明済み。
- **除外維持** — `prose` L330–335: 標準例の箇条書きを導入する見出し文だけで、数学的主張や局所的証明を含まない。
- **除外維持** — `prose` L337–346: Setの2値分類子という標準的な背景例とpresheaf記号のmathmeta宣言。集合の分類子をここで新たに構成・証明する段落ではなく、章頭で指定したMac Lane–Moerdijkの基本例である。
- **除外維持** — `prose` L348–363: presheafの篩、sheafの開集合、実現可能性という標準例の概説。Mac Lane–Moerdijk、van Oosten、および後続の具体的計算への参照であり、一般presheaf/sheafトポスの定理をこの付録の局所的証明とは扱わない。
- **除外維持** — `prose` L388–397: Mitchell–Bénabou内部言語の一般存在を紹介する背景。章頭のMac Lane–Moerdijkおよび末尾のPittsを参照する一般圏論的論理であり、全初等トポスの高階論理の健全性を局所的に形式化済みとは主張しない。
- **除外維持** — `prose` L415–450: 任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。
- **除外維持** — `prose` L452–465: 任意の初等トポスの量化子随伴とBeck–Chevalleyという一般内部言語の理論。Mac Lane–Moerdijk/Pittsを外部背景として使い、局所証明を提示しない。PCA triposの量化子の実装・随伴・BC証明は後続の別命題で実際に接続している。
- **除外維持** — `prose` L467–477: power object、対角線、内包・記述を含む高階内部言語の一般的意味論の概説で、Mac Lane–Moerdijk/Pittsの外部理論。具体的なPCA関係の局所計算から全一般健全性を証明したとは扱わない。
- **除外維持** — `prose` L479–494: Booleanトポス、sheafの例、内部ACと外部のepi分裂の区別という一般的な背景説明。Mac Lane–Moerdijk/van Oostenと明示的な有効トポス章への参照であり、この段落で新たな反例の証明を提示しない。参照先の具体的な非一様性の証明は独立に監査する。
- **除外維持** — `prose` L496–510: 全初等トポスに対する内部高階論理の健全性はMac Lane–Moerdijk/Pittsの外部定理。CT・MPのtrackerやKLS/Ceitinが別途必要という参照案内であり、それらがトポス公理だけから従うとはしない。本文に局所的な健全性証明やKLS証明はない。
- **除外維持** — `prose` L514–525: PCAの導入とFeferman、K1、K2の歴史的背景。実際のPCA公理と抽象化の局所的証明は直後のdefinition/proposition/proofで独立に接続済み。この歴史紹介から各モデルの構成を一括して形式化済みとはしない。
- **除外維持** — `prose` L591–604: 遅延固定点および再帰的定義可能性の標準結果はBauer §2.5への明示的引用による外部入力。PCAAbstractionの抽象化・proper-prefix definednessだけで遅延固定点を証明済みとしない。局所的に実際に構成したpair/selector/case等は後続の別証明で接続済み。
- **除外維持** — `prose` L688–702: K2と任意tracker/計算可能部分代数の区別はBauer §3.5.5の明示的引用によるモデル比較。本文はK2の組合子やrelative realizabilityを局所的に構成・証明しない。数値lambda添字のK1構成とは区別する。
- **除外維持** — `prose` L704–713: Scott powerset、D∞、coalgebraicなどのPCAの例を列挙する文献的背景で、具体的構成・性質の証明を提示していない。各PCAからトポスを得る一般定理は明示的に後のtripos-to-topos定理に委ね、局所構成と区別する。
- **除外維持** — `prose` L1078–1088: triposの歴史と構成の動機付けの概説。Hyland–Johnstone–Pitts、van Oostenの一般理論に関する背景で、ここで具体的なfree-completionの普遍性を証明してはいない。実際のPCA tripos/PER構成は後続で独立に監査済み。
- **除外維持** — `prose` L1110–1118: triposの各要素の論理的な読み方と一般高階意味論の標準的説明。SetTriposの公理およびPCAの実際の実装は別箇所で接続し、一般の高階健全性はPitts/van Oostenの外部理論として扱う。
- **除外維持** — `prose` L1208–1225: 任意triposに対する標準PER完成の定義を紹介する外部一般理論。直後で一般tripos-to-topos定理を用いる旨を明示し、van Oosten/Pittsを参照する。この付録で局所的に証明する任意PCA上のRealizerPER、FunctionalRelation、相互一様含意の商、category lawsは独立した命題・証明に接続済みで、一般tripos全体の実装と同一視しない。
- **除外維持** — `prose` L1227–1236: 一般tripos-to-topos定理を呼び出す箇所として本文自身が明示する外部入力。van Oosten/Pittsの一般定理を局所証明したとは扱わず、指定されていない普遍性も主張しない。具体的PCAと有効トポスのPER計算は別に監査する。
- **除外維持** — `prose` L1633–1649: 一般PCAごとの実現可能性モデルを比較する結びの概説。K2やdomainモデルは文献的背景で、一般tripos-to-topos定理の外部入力に依存する。TTE/domainとの圏同値を主張しない旨も明示され、追加の局所的構成・証明を提示しない。
- **除外維持** — `prose` L1654–1663: Goldblatt、Mac Lane–Moerdijk、Pittsの文献を選ぶための読書案内だけで、追加の局所的証明ではない。
- **除外維持** — `prose` L1665–1674: KunenとGaoへの読書案内だけで、追加の局所的構成・証明ではない。
- **除外維持** — `prose` L1676–1684: van OostenとBauerの実現可能性文献への読書案内だけで、追加の局所的証明ではない。

## 再確認

判定は `coverage-scope-review.json` に保持する。本文段落または前後の文脈を含む章ファイルが変われば判定を失効させる。
`python3 tools/booklink_audit.py --out build/coverage-audit` が全件の取りこぼしと失効を確認し、同ディレクトリに `scope-review.md` を出力する。
失効した判定: 0 件。
