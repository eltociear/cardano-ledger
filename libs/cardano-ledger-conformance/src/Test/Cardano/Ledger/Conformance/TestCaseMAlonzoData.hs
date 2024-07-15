module Test.Cardano.Ledger.Conformance.TestCaseMAlonzoData
where

import Lib
import Test.Cardano.Ledger.Conformance.Orphans ()

-- seed 860738573
regDRepErrorTestData :: (CertEnv, GState, TxCert)
regDRepErrorTestData = (regDRepEnv, regDRepState, regDRepSignal)

-- seed 234853314
updateDRepErrorTestData :: (CertEnv, GState, TxCert)
updateDRepErrorTestData = (updateDRepEnv, updateDRepState, updateDRepSignal)

regDRepEnv :: CertEnv
regDRepEnv =
  MkCertEnv
    { epoch = 0
    , pp =
        MkPParams
          { ppA = 0
          , ppB = 0
          , ppMaxBlockSize = 1
          , ppMaxTxSize = 1
          , ppMaxHeaderSize = 1
          , ppMaxValSize = 1
          , ppMinUTxOValue = 0
          , ppPoolDeposit = 1
          , ppKeyDeposit = 0
          , ppEmax = 1
          , ppNopt = 0
          , ppPv = (0, 0)
          , ppPoolVotingThresholds =
              MkPoolThresholds
                (302026859883347689, 1000000000000000000)
                (21, 50)
                (3143, 10000)
                (94900396147140797, 2500000000000000000)
                (7, 10)
          , ppDrepVotingThresholds =
              MkDrepThresholds
                (300187137, 2500000000)
                (10253, 500000)
                (1, 5)
                (1, 1)
                (5424043, 50000000)
                (21489819003023, 25000000000000)
                (4889832021, 5000000000)
                (16, 25)
                (1483639521139196927, 5000000000000000000)
                (64437278629, 100000000000)
          , ppGovActionLifetime = 1
          , ppGovActionDeposit = 1
          , ppDrepDeposit = 1
          , ppDrepActivity = 0
          , ppCCMinSize = 0
          , ppCCMaxTermLength = 1
          , ppCostmdls = ()
          , ppPrices = ()
          , ppMaxTxExUnits = (0, 0)
          , ppMaxBlockExUnits = (0, 0)
          , ppCoinsPerUTxOByte = 0
          , ppMaxCollateralInputs = 0
          }
    , votes =
        [ MkGovVote
            { gvGid = (MkTxId 115226901456195599427884820575782413276072611530428351923844282107126212407004, 2)
            , gvVoter =
                (SPO, (KeyHashObj 14851458826130131743637198527587984388725556383364516954870199704468))
            , gvVote = VoteNo
            , gvAnchor = Just ()
            }
        , MkGovVote
            { gvGid = (MkTxId 88083199499963725752216630727442965110458204362360448264871550469052603482426, 2)
            , gvVoter =
                (SPO, (KeyHashObj 21080582599226838175513894122043164386946890654269623458841004455554))
            , gvVote = VoteYes
            , gvAnchor = Just ()
            }
        , MkGovVote
            { gvGid = (MkTxId 88448952286881031788909683605842369707461139360686836686092501843181962438196, 1)
            , gvVoter =
                (SPO, (KeyHashObj 21080582599226838175513894122043164386946890654269623458841004455554))
            , gvVote = VoteAbstain
            , gvAnchor = Just ()
            }
        ]
    , wdrls =
        MkHSMap
          [
            ( ((), ScriptObj 863628978550658778806118175557780864010495978784202428861811426725)
            , 341732
            )
          ,
            ( ((), KeyHashObj 5850959069843765096279864785780096551531339390830885497783677333467)
            , 310379
            )
          ]
    }

regDRepState :: GState
regDRepState = MkGState {dreps = MkHSMap [], ccHotKeys = MkHSMap []}

regDRepSignal :: TxCert
regDRepSignal =
  RegDRep
    (ScriptObj 17525304867231275649772775250368064047039405927693313776739084043872)
    1
    ()

updateDRepEnv :: CertEnv
updateDRepEnv =
  MkCertEnv
    { epoch = 0
    , pp =
        MkPParams
          { ppA = 0
          , ppB = 0
          , ppMaxBlockSize = 1
          , ppMaxTxSize = 1
          , ppMaxHeaderSize = 1
          , ppMaxValSize = 1
          , ppMinUTxOValue = 0
          , ppPoolDeposit = 1
          , ppKeyDeposit = 0
          , ppEmax = 1
          , ppNopt = 0
          , ppPv = (0, 0)
          , ppPoolVotingThresholds =
              MkPoolThresholds
                (53101, 100000)
                (78, 125)
                (613404331414007, 10000000000000000)
                (0, 1)
                (1, 20)
          , ppDrepVotingThresholds =
              MkDrepThresholds
                (390926947, 2000000000)
                (589, 1000)
                (371, 1000)
                (1660491, 8000000)
                (2, 5)
                (651269191959751, 781250000000000)
                (1, 5)
                (765049163510351, 5000000000000000)
                (149643330670816993, 200000000000000000)
                (1925077578881961721, 2500000000000000000)
          , ppGovActionLifetime = 1
          , ppGovActionDeposit = 1
          , ppDrepDeposit = 1
          , ppDrepActivity = 0
          , ppCCMinSize = 0
          , ppCCMaxTermLength = 1
          , ppCostmdls = ()
          , ppPrices = ()
          , ppMaxTxExUnits = (0, 0)
          , ppMaxBlockExUnits = (0, 0)
          , ppCoinsPerUTxOByte = 0
          , ppMaxCollateralInputs = 0
          }
    , votes =
        [ MkGovVote
            { gvGid = (MkTxId 10573480762785547458715593906319493592515577657358578529188644420493312467314, 3)
            , gvVoter =
                (CC, (KeyHashObj 22413119276237102406895649365844197611424564549865197580618963945526))
            , gvVote = VoteYes
            , gvAnchor = Just ()
            }
        , MkGovVote
            { gvGid = (MkTxId 61950260584406258828631380615546504229797558998895154032220297161010314086039, 2)
            , gvVoter =
                (CC, (KeyHashObj 22413119276237102406895649365844197611424564549865197580618963945526))
            , gvVote = VoteNo
            , gvAnchor = Nothing
            }
        , MkGovVote
            { gvGid = (MkTxId 22248136101902996774702417930112075297377726522206941548782298778735160712238, 2)
            , gvVoter =
                (SPO, (KeyHashObj 15533166275809003337758353294689354602794597660954287114354176080950))
            , gvVote = VoteNo
            , gvAnchor = Nothing
            }
        , MkGovVote
            { gvGid = (MkTxId 52590512554131303501102878660554949338059068610568044970289942186060195155377, 1)
            , gvVoter =
                (SPO, (KeyHashObj 15533166275809003337758353294689354602794597660954287114354176080950))
            , gvVote = VoteNo
            , gvAnchor = Just ()
            }
        , MkGovVote
            { gvGid = (MkTxId 89992703712414083318900191501311711222345798071743105811413652426283655760265, 2)
            , gvVoter =
                (SPO, (KeyHashObj 15533166275809003337758353294689354602794597660954287114354176080950))
            , gvVote = VoteNo
            , gvAnchor = Just ()
            }
        ]
    , wdrls =
        MkHSMap
          [
            ( ((), ScriptObj 11351610118471723845378736158885299317678859208838805025566956462847)
            , 246955
            )
          ,
            ( ((), KeyHashObj 14855755521937664048965594005142031367119049395668203891461311889243)
            , 8730
            )
          ,
            ( ((), KeyHashObj 23509965346913385229618864767350023943841938458880348162822738262631)
            , 603880
            )
          ,
            ( ((), KeyHashObj 22007813242956090588149408724251297307777000571636872648320033253196)
            , 264632
            )
          ]
    }

updateDRepState :: GState
updateDRepState =
  MkGState {
    dreps = MkHSMap
      [
        ( KeyHashObj 15620926545167659031442662663354207712010596339992188535497801183352, 0)
      ],
    ccHotKeys = MkHSMap []
  }

updateDRepSignal :: TxCert
updateDRepSignal =
  RegDRep
    (KeyHashObj 15620926545167659031442662663354207712010596339992188535497801183352)
    0
    ()
