window.BENCHMARK_DATA = {
  "lastUpdate": 1710349279090,
  "repoUrl": "https://github.com/IntersectMBO/cardano-ledger",
  "entries": {
    "Haskell Benchmark": [
      {
        "commit": {
          "author": {
            "email": "teodora.danciu@tweag.io",
            "name": "teodanciu",
            "username": "teodanciu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0adeff37a9dd68bc95c1eedb95bfccd2cd42f8e5",
          "message": "Merge pull request #4194 from IntersectMBO/td/fix-imp-epoch-check\n\nFix epoch boundary check in ImpTest",
          "timestamp": "2024-03-13T16:56:24Z",
          "tree_id": "a9e2531fa1660821f763d4f9dbb89459d29303f1",
          "url": "https://github.com/IntersectMBO/cardano-ledger/commit/0adeff37a9dd68bc95c1eedb95bfccd2cd42f8e5"
        },
        "date": 1710349274760,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "applyTxBenchmarks/ApplyTxInEra/ShelleyEra C_Crypto",
            "value": 0.00006653688699454258,
            "unit": "Nanoseconds",
            "range": 0.0000027941655894636263
          },
          {
            "name": "applyTxBenchmarks/ApplyTxInEra/AllegraEra C_Crypto",
            "value": 0.00007102970410863693,
            "unit": "Nanoseconds",
            "range": 4.701267694090584e-7
          },
          {
            "name": "applyTxBenchmarks/ApplyTxInEra/MaryEra C_Crypto",
            "value": 0.00008031928297924465,
            "unit": "Nanoseconds",
            "range": 0.0000011874038592347818
          },
          {
            "name": "applyTxBenchmarks/ApplyTxInEra/AlonzoEra C_Crypto",
            "value": 0.00011317939362091532,
            "unit": "Nanoseconds",
            "range": 5.561066943087761e-7
          },
          {
            "name": "applyTxBenchmarks/Deserialise Shelley Tx/ShelleyEra C_Crypto",
            "value": 0.000010771239864678119,
            "unit": "Nanoseconds",
            "range": 4.001442630838303e-7
          },
          {
            "name": "applyTxBenchmarks/Deserialise Shelley Tx/AllegraEra C_Crypto",
            "value": 0.000018839925779572042,
            "unit": "Nanoseconds",
            "range": 4.304018738144683e-7
          },
          {
            "name": "applyTxBenchmarks/Deserialise Shelley Tx/MaryEra C_Crypto",
            "value": 0.000018081228673674924,
            "unit": "Nanoseconds",
            "range": 6.702032216366104e-7
          },
          {
            "name": "applyTxBenchmarks/Deserialise Shelley Tx/AlonzoEra C_Crypto",
            "value": 0.00000883450082030173,
            "unit": "Nanoseconds",
            "range": 8.653421534419393e-8
          }
        ]
      }
    ]
  }
}