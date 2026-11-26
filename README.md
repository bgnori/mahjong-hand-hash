# Mahjong hand hash

Experimental keys for Mahjong hands, using normalized tile types from
`mahjong-domain-core`. Import `MahjongHandHash` or
`MahjongHandHash.HandKey`; the existing declarations remain in the
`MahjongDomain` namespace.

See the [glossary](docs/GLOSSARY.md) for the planned key names and their
meanings.

The implementation is a draft. Encode/decode calls check the non-negative
signed INT64 range and verify their inverse operation at runtime; the
key-space bounds are also tested. The meld-aware key lacks full formal proofs,
regression tests are not comprehensive, and the encoding is not versioned. A
previously reported collision in meld-combination ranking has been corrected
and covered by a regression test. Do not use its keys as persistent
identifiers until the encoding has been fully verified and versioned.

`MeldAwareHandKey.encode` accepts the shared `MahjongDomain.HandSnapshot`;
`decode` returns the same shared representation, with melds in canonical key
order. Hand identity ignores meld order but retains duplicates and call details.
Inputs are checked for fixed-meld count, standing size and combined four-copy
capacity. The current ranking remains experimental and its full correctness
has not been proved.

For tile-count keys, Lean proves the candidate count for up to 34 tile kinds
and 18 tiles, successful encoding, round-trip recovery, injectivity, and the
INT64 range for every valid input. Decode succeeds exactly for non-negative
keys below `keyMax`, returns valid counts, and re-encodes to the same key.
Thus there are no holes in the assigned tile-count key interval.

The Lean regression job requires at least one `.lean` file under
`MahjongHandHashTests/` and builds the `MahjongHandHash` and
`MahjongHandHashTests` Lake targets. A sibling checkout of
`mahjong-domain-core` is required. The presence check prevents an empty test
directory from passing; it does not determine whether a test is meaningful.
