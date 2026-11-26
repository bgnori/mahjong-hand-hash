# Mahjong hand hash

Experimental keys for Mahjong hands, using normalized tile types from
`mahjong-domain-core`. Import `MahjongHandHash` or
`MahjongHandHash.HandKey`; the existing declarations remain in the
`MahjongDomain` namespace.

See the [glossary](docs/GLOSSARY.md) for the planned key names and their
meanings.

The implementation is a draft. Encode/decode calls check the non-negative
signed INT64 range and verify their inverse operation at runtime; the
key-space bounds are also tested. Full formal proofs and comprehensive
regression tests are not yet present, and the encoding is not versioned. A
previously reported collision in meld-combination ranking has been corrected
and covered by a regression test. Do not use its keys as persistent
identifiers until the encoding has been fully verified and versioned.

For tile-count keys, Lean proves the candidate count for up to 34 tile kinds
and 18 tiles, successful encoding, round-trip recovery, injectivity, and the
INT64 range for every valid input. A successfully decoded key also re-encodes
to the same key. It remains unproven that every non-negative key below
`keyMax` decodes successfully (i.e. that the key space has no holes).

The Lean regression job requires at least one `.lean` file under
`MahjongHandHashTests/` and builds the `MahjongHandHash` and
`MahjongHandHashTests` Lake targets. A sibling checkout of
`mahjong-domain-core` is required. The presence check prevents an empty test
directory from passing; it does not determine whether a test is meaningful.
