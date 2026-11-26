# Mahjong Hand Hash Glossary / 牌姿キー用語集

This glossary describes hand-hash-specific concepts. Shared tile and hand
terminology is defined by the
[Mahjong Domain Core glossary](https://github.com/bgnori/mahjong-domain-core/blob/main/docs/GLOSSARY.md).
`TileCountsKey` is implemented as a distinct key type. The planned
`MeldAwareHandKey` is still named `MeldedHandKey` in the draft implementation.

この用語集はhand hash固有の概念を記述します。牌や手牌の共通用語は
[Mahjong Domain Coreの用語集](https://github.com/bgnori/mahjong-domain-core/blob/main/docs/GLOSSARY.md)
を参照してください。`TileCountsKey`は別のキー型として実装済みです。
予定名`MeldAwareHandKey`は試案の実装ではまだ`MeldedHandKey`を使用しています。

| Name / 名称 | 日本語 | Definition and scope / 定義・対象範囲 |
|---|---|---|
| `TileCountsKey` | 牌集合キー | A key for the normalized tile-kind counts of all hand-held and fixed-meld tiles. It forgets the distinction between them and the meld details. / 手牌と固定面子の全牌を合わせた正規化牌種ごとの枚数を表すキー。手牌と固定面子の区別や面子の詳細は保持しません。 |
| `MeldAwareHandKey` | 鳴き込みキー | A key for hand-held tile counts and an unordered collection of fixed melds, including called-tile, caller, and kan-kind information where applicable. A hand with no fixed melds is also included. / 手牌の牌種ごとの枚数と、固定面子の順序を無視した組を表すキー。該当する場合は鳴き牌、鳴き元、槓の種類も保持し、固定面子がない牌姿も対象です。 |

Both key spaces normalize red fives and ignore the order of fixed melds.
They are distinct spaces and their numeric values must not be compared as
equivalent. A kan contributes four physical tiles to the counts. The planned
`TileCountsKey` domain also includes count vectors with 13–18 tiles and at
most four of each kind, even when no corresponding meld-aware hand exists.

どちらも赤5を正規化し、固定面子の順序を区別しません。両者は別のキー空間であり、
数値をそのまま同一視してはなりません。槓は実際の4枚として数えます。
`TileCountsKey`の予定する定義域は、対応する鳴き込み牌姿が存在しない場合も含め、
合計13〜18枚かつ各牌種4枚以下のカウントです。
