{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Conformance.Orphans where

import Data.Bifunctor (Bifunctor (..))
import Data.Default.Class (Default)
import Data.List (nub, sortOn)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Lib
import Test.Cardano.Ledger.Common (NFData, ToExpr)
import Test.Cardano.Ledger.Conformance.SpecTranslate.Core (FixupSpecRep (..), OpaqueErrorString)
import Test.Cardano.Ledger.Conformance.Utils
import Test.Cardano.Ledger.Conway.TreeDiff (Expr (..), ToExpr (..))

deriving instance Generic (HSSet a)

deriving instance Generic GovActionState

deriving instance Generic Vote

deriving instance Generic GovProposal

deriving instance Generic GovAction

deriving instance Generic GovVote

deriving instance Generic GovSignal

deriving instance Generic GovEnv

deriving instance Generic EnactState

deriving instance Generic DepositPurpose

deriving instance Generic CertEnv

deriving instance Generic CertEnv'

deriving instance Generic PState

deriving instance Generic DState

deriving instance Generic DState'

deriving instance Generic GState

deriving instance Generic GState'

deriving instance Generic CertState

deriving instance Generic CertState'

deriving instance Generic RatifyEnv

deriving instance Generic RatifyState

deriving instance Generic StakeDistrs

deriving instance Generic EnactEnv

deriving instance Generic DelegEnv

deriving instance Generic DelegEnv'

deriving instance Generic PoolThresholds

deriving instance Generic DrepThresholds

deriving instance Generic NewEpochEnv

deriving instance Generic EpochState

deriving instance Generic Snapshots

deriving instance Generic Snapshot

deriving instance Generic LedgerState

deriving instance Generic Acnt

deriving instance Generic RewardUpdate

deriving instance Generic NewEpochState

deriving instance Ord DepositPurpose

deriving instance Ord Tag

deriving instance Ord Credential

deriving instance Ord GovRole

deriving instance Ord VDeleg

deriving instance Ord Vote

deriving instance Ord PoolThresholds

deriving instance Ord DrepThresholds

deriving instance Ord PParamsUpdate

deriving instance Ord GovAction

deriving instance Ord GovActionState

deriving instance Eq a => Eq (HSSet a)

deriving instance Eq AgdaEmpty

deriving instance Eq TxBody

deriving instance Eq Tag

deriving instance Eq TxWitnesses

deriving instance Eq Tx

deriving instance Eq PoolThresholds

deriving instance Eq DrepThresholds

deriving instance Eq PParams

deriving instance Eq UTxOState

deriving instance Eq PParamsUpdate

deriving instance Eq GovAction

deriving instance Eq GovVote

deriving instance Eq GovSignal

deriving instance Eq GovProposal

deriving instance Eq Vote

deriving instance Eq GovActionState

deriving instance Eq GovEnv

deriving instance Eq EnactState

deriving instance Eq UTxOEnv

deriving instance Eq DepositPurpose

deriving instance Eq CertEnv

deriving instance Eq CertEnv'

deriving instance Eq DState

deriving instance Eq DState'

deriving instance Eq PState

deriving instance Eq GState

deriving instance Eq GState'

deriving instance Eq CertState

deriving instance Eq CertState'

deriving instance Eq RatifyState

deriving instance Eq EpochState

deriving instance Eq Snapshots

deriving instance Eq Snapshot

deriving instance Eq Acnt

deriving instance Eq LedgerState

deriving instance Eq RewardUpdate

deriving instance Eq NewEpochState

instance (NFData k, NFData v) => NFData (HSMap k v)

instance NFData a => NFData (HSSet a)

instance NFData PParamsUpdate

instance NFData GovAction

instance NFData TxId

instance NFData UTxOState

instance NFData Vote

instance NFData Credential

instance NFData GovRole

instance NFData GovActionState

instance NFData AgdaEmpty

instance NFData GovVote

instance NFData GovProposal

instance NFData GovSignal

instance NFData DrepThresholds

instance NFData PoolThresholds

instance NFData PParams

instance NFData EnactState

instance NFData GovEnv

instance NFData VDeleg

instance NFData TxCert

instance NFData TxBody

instance NFData Tag

instance NFData TxWitnesses

instance NFData Tx

instance NFData UTxOEnv

instance NFData DepositPurpose

instance NFData CertEnv

instance NFData CertEnv'

instance NFData PState

instance NFData DState

instance NFData DState'

instance NFData GState

instance NFData GState'

instance NFData CertState

instance NFData CertState'

instance NFData StakeDistrs

instance NFData RatifyEnv

instance NFData RatifyState

instance NFData EnactEnv

instance NFData DelegEnv

instance NFData DelegEnv'

instance NFData NewEpochEnv

instance NFData EpochState

instance NFData Snapshots

instance NFData Snapshot

instance NFData Acnt

instance NFData LedgerState

instance NFData RewardUpdate

instance NFData NewEpochState

instance ToExpr a => ToExpr (HSSet a)

instance ToExpr Credential where
  toExpr (KeyHashObj h) = App "KeyHashObj" [agdaHashToExpr 28 h]
  toExpr (ScriptObj h) = App "ScriptObj" [agdaHashToExpr 28 h]

instance (ToExpr k, ToExpr v) => ToExpr (HSMap k v)

instance ToExpr PParamsUpdate

instance ToExpr GovAction

instance ToExpr GovRole

instance ToExpr Vote

instance ToExpr TxId where
  toExpr (MkTxId x) = App "TxId" [agdaHashToExpr 32 x]

instance ToExpr GovActionState

instance ToExpr GovProposal

instance ToExpr GovVote

instance ToExpr GovSignal

instance ToExpr PoolThresholds

instance ToExpr DrepThresholds

instance ToExpr PParams

instance ToExpr GovEnv

instance ToExpr EnactState

instance ToExpr VDeleg

instance ToExpr TxCert

instance ToExpr TxBody

instance ToExpr AgdaEmpty

instance ToExpr Tag

instance ToExpr TxWitnesses

instance ToExpr Tx

instance ToExpr UTxOState

instance ToExpr UTxOEnv

instance ToExpr DepositPurpose

instance ToExpr CertEnv

instance ToExpr CertEnv'

instance ToExpr DState

instance ToExpr DState'

instance ToExpr PState

instance ToExpr GState

instance ToExpr GState'

instance ToExpr CertState

instance ToExpr CertState'

instance ToExpr StakeDistrs

instance ToExpr RatifyEnv

instance ToExpr RatifyState

instance ToExpr EnactEnv

instance ToExpr DelegEnv

instance ToExpr DelegEnv'

instance ToExpr NewEpochEnv

instance ToExpr EpochState

instance ToExpr Snapshots

instance ToExpr Snapshot

instance ToExpr LedgerState

instance ToExpr Acnt

instance ToExpr RewardUpdate

instance ToExpr NewEpochState

instance Default (HSMap k v)

instance FixupSpecRep OpaqueErrorString

instance FixupSpecRep a => FixupSpecRep [a]

instance FixupSpecRep Char where
  fixup = id

instance
  ( Eq v
  , Ord k
  , FixupSpecRep k
  , FixupSpecRep v
  ) =>
  FixupSpecRep (HSMap k v)
  where
  fixup (MkHSMap l) = MkHSMap . sortOn fst $ bimap fixup fixup <$> nub l

instance (Ord a, FixupSpecRep a) => FixupSpecRep (HSSet a) where
  fixup (MkHSSet l) = MkHSSet . Set.toList . Set.fromList $ fixup <$> l

instance (FixupSpecRep a, FixupSpecRep b) => FixupSpecRep (a, b)

instance FixupSpecRep a => FixupSpecRep (Maybe a)

instance (FixupSpecRep a, FixupSpecRep b) => FixupSpecRep (Either a b)

instance FixupSpecRep Integer where
  fixup = id

instance FixupSpecRep Bool

instance FixupSpecRep TxId

instance FixupSpecRep ()

instance FixupSpecRep UTxOState

instance FixupSpecRep Credential

instance FixupSpecRep GovRole

instance FixupSpecRep VDeleg

instance FixupSpecRep DepositPurpose

instance FixupSpecRep DState

instance FixupSpecRep DState'

instance FixupSpecRep PState

instance FixupSpecRep GState

instance FixupSpecRep GState'

instance FixupSpecRep CertState

instance FixupSpecRep CertState'

instance FixupSpecRep Vote

instance FixupSpecRep PParamsUpdate

instance FixupSpecRep GovAction

instance FixupSpecRep GovActionState

instance FixupSpecRep AgdaEmpty

instance FixupSpecRep StakeDistrs

instance FixupSpecRep PoolThresholds

instance FixupSpecRep DrepThresholds

instance FixupSpecRep PParams

instance FixupSpecRep EnactState

instance FixupSpecRep RatifyEnv

instance FixupSpecRep RatifyState

instance FixupSpecRep EpochState

instance FixupSpecRep Snapshots

instance FixupSpecRep Snapshot

instance FixupSpecRep Acnt

instance FixupSpecRep LedgerState

instance FixupSpecRep RewardUpdate

instance FixupSpecRep NewEpochState
