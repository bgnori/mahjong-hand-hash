# Mahjong hand hash

Reversible keys for Mahjong hands. The initial project contains no implementation
or regression tests, so CI intentionally fails its test-presence check.

The Lean regression job requires at least one `.lean` file under
`MahjongHandHashTests/` and builds the `MahjongHandHash` and
`MahjongHandHashTests` Lake targets. A sibling checkout of
`mahjong-domain-core` is required. The presence check prevents an empty test
directory from passing; it does not determine whether a test is meaningful.
