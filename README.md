# Mahjong hand hash

Experimental keys for Mahjong hands, using normalized tile types from
`mahjong-domain-core`. Import `MahjongHandHash` or
`MahjongHandHash.HandKey`; the existing declarations remain in the
`MahjongDomain` namespace.

The implementation is a draft: round-trip and injectivity proofs, full bounds
proofs, and comprehensive regression tests are not yet present. A previously
reported collision in meld-combination ranking has been corrected and covered
by a regression test, but the encoding is not fully proven or versioned. Do
not use its keys as persistent identifiers until the encoding has been
verified and versioned.

The Lean regression job requires at least one `.lean` file under
`MahjongHandHashTests/` and builds the `MahjongHandHash` and
`MahjongHandHashTests` Lake targets. A sibling checkout of
`mahjong-domain-core` is required. The presence check prevents an empty test
directory from passing; it does not determine whether a test is meaningful.
