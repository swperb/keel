| model | mode | pass | silent failures | not done | contract altered | proved obligations | spec lines | avg toolchain runs | agent tokens | agent seconds |
|---|---|---|---|---|---|---|---|---|---|---|
| haiku | keel | 6/6 | 0 | 0 | - | 163 | 52 | 1.5 | 95404 | 211.4 |
| haiku | keel-given | 6/6 | 0 | 0 | 0 | 339 | 137 | 1.0 | 118756 | 322.6 |
| haiku | rust | 6/6 | 0 | 0 | - | 0 | 0 | 2.0 | 68268 | 69.4 |
| opus | keel | 5/6 | 1 | 0 | - | 332 | 109 | 1.5 | 65405 | 136.8 |
| opus | keel-given | 6/6 | 0 | 0 | 0 | 342 | 133 | 1.2 | 76655 | 188.4 |
| opus | rust | 6/6 | 0 | 0 | - | 0 | 0 | 1.0 | 53559 | 28.4 |
| sonnet | keel | 6/6 | 0 | 0 | - | 294 | 117 | 1.7 | 66205 | 121.4 |
| sonnet | keel-given | 6/6 | 0 | 0 | 0 | 332 | 125 | 1.3 | 69273 | 104.4 |
| sonnet | rust | 6/6 | 0 | 0 | - | 0 | 0 | 1.0 | 53196 | 25.1 |

| model | mode | task | self_ok | outcome | proved | detail |
|---|---|---|---|---|---|---|
| haiku | keel | 07-rotate | True | pass | 18 |  |
| haiku | keel | 08-dedup | True | pass | 21 |  |
| haiku | keel | 09-union | True | pass | 26 |  |
| haiku | keel | 10-partition | True | pass | 30 |  |
| haiku | keel | 11-windows | True | pass | 52 |  |
| haiku | keel | 12-vending | True | pass | 16 |  |
| haiku | keel-given | 07-rotate | True | pass | 32 |  |
| haiku | keel-given | 08-dedup | True | pass | 35 |  |
| haiku | keel-given | 09-union | True | pass | 49 |  |
| haiku | keel-given | 10-partition | True | pass | 64 |  |
| haiku | keel-given | 11-windows | True | pass | 83 |  |
| haiku | keel-given | 12-vending | True | pass | 76 |  |
| haiku | rust | 07-rotate | True | pass | 0 |  |
| haiku | rust | 08-dedup | True | pass | 0 |  |
| haiku | rust | 09-union | True | pass | 0 |  |
| haiku | rust | 10-partition | True | pass | 0 |  |
| haiku | rust | 11-windows | True | pass | 0 |  |
| haiku | rust | 12-vending | True | pass | 0 |  |
| opus | keel | 07-rotate | True | pass | 28 |  |
| opus | keel | 08-dedup | True | harness_reject | 42 | V-UNKNOWN |
| opus | keel | 09-union | True | pass | 52 |  |
| opus | keel | 10-partition | True | pass | 48 |  |
| opus | keel | 11-windows | True | pass | 58 |  |
| opus | keel | 12-vending | True | pass | 104 |  |
| opus | keel-given | 07-rotate | True | pass | 31 |  |
| opus | keel-given | 08-dedup | True | pass | 39 |  |
| opus | keel-given | 09-union | True | pass | 75 |  |
| opus | keel-given | 10-partition | True | pass | 47 |  |
| opus | keel-given | 11-windows | True | pass | 74 |  |
| opus | keel-given | 12-vending | True | pass | 76 |  |
| opus | rust | 07-rotate | True | pass | 0 |  |
| opus | rust | 08-dedup | True | pass | 0 |  |
| opus | rust | 09-union | True | pass | 0 |  |
| opus | rust | 10-partition | True | pass | 0 |  |
| opus | rust | 11-windows | True | pass | 0 |  |
| opus | rust | 12-vending | True | pass | 0 |  |
| sonnet | keel | 07-rotate | True | pass | 29 |  |
| sonnet | keel | 08-dedup | True | pass | 41 |  |
| sonnet | keel | 09-union | True | pass | 62 |  |
| sonnet | keel | 10-partition | True | pass | 54 |  |
| sonnet | keel | 11-windows | True | pass | 68 |  |
| sonnet | keel | 12-vending | True | pass | 40 |  |
| sonnet | keel-given | 07-rotate | True | pass | 35 |  |
| sonnet | keel-given | 08-dedup | True | pass | 38 |  |
| sonnet | keel-given | 09-union | True | pass | 56 |  |
| sonnet | keel-given | 10-partition | True | pass | 52 |  |
| sonnet | keel-given | 11-windows | True | pass | 75 |  |
| sonnet | keel-given | 12-vending | True | pass | 76 |  |
| sonnet | rust | 07-rotate | True | pass | 0 |  |
| sonnet | rust | 08-dedup | True | pass | 0 |  |
| sonnet | rust | 09-union | True | pass | 0 |  |
| sonnet | rust | 10-partition | True | pass | 0 |  |
| sonnet | rust | 11-windows | True | pass | 0 |  |
| sonnet | rust | 12-vending | True | pass | 0 |  |
