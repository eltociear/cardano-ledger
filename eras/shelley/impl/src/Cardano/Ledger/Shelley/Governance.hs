{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Cardano.Ledger.Shelley.Governance (
  EraGov (..),
  ShelleyGovState (..),
  emptyShelleyGovState,
  FuturePParams (..),
  solidifyFuturePParams,
  maybeFuturePParams,
  nextEpochPParams,
  -- Lens
  proposalsL,
  futureProposalsL,
  curPParamsShelleyGovStateL,
  prevPParamsShelleyGovStateL,
  futurePParamsShelleyGovStateL,

  -- * Deprecations
  proposals,
  futureProposals,
  sgovPp,
  sgovPrevPp,
) where

import Cardano.Ledger.Binary (
  DecCBOR (decCBOR),
  DecShareCBOR (..),
  EncCBOR (encCBOR),
  FromCBOR (..),
  ToCBOR (..),
  decNoShareCBOR,
 )
import Cardano.Ledger.Binary.Coders (Decode (..), Encode (..), decode, encode, (!>), (<!))
import Cardano.Ledger.CertState (Obligations)
import Cardano.Ledger.Core
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Shelley.Era (ShelleyEra)
import Cardano.Ledger.Shelley.PParams (ProposedPPUpdates, emptyPPPUpdates)
import Cardano.Ledger.Tools
import Control.DeepSeq (NFData (..))
import Data.Aeson (
  KeyValue,
  ToJSON (..),
  object,
  pairs,
  (.=),
 )
import Data.Default.Class (Default (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Typeable
import GHC.Generics (Generic)
import Lens.Micro (Lens', lens, (^.))
import NoThunks.Class (NoThunks (..))

class
  ( EraPParams era
  , Eq (GovState era)
  , Show (GovState era)
  , NoThunks (GovState era)
  , NFData (GovState era)
  , EncCBOR (GovState era)
  , DecCBOR (GovState era)
  , DecShareCBOR (GovState era)
  , ToCBOR (GovState era)
  , FromCBOR (GovState era)
  , Default (GovState era)
  , ToJSON (GovState era)
  ) =>
  EraGov era
  where
  type GovState era = (r :: Type) | r -> era

  -- | Construct empty governance state
  emptyGovState :: GovState era
  emptyGovState = def

  -- | Returns `Nothing` for all eras starting with Conway, otherwise returns proposed
  -- pparams updates
  getProposedPPUpdates :: GovState era -> Maybe (ProposedPPUpdates era)
  getProposedPPUpdates _ = Nothing

  -- | Lens for accessing current protocol parameters
  curPParamsGovStateL :: Lens' (GovState era) (PParams era)

  -- | Lens for accessing the previous protocol parameters
  prevPParamsGovStateL :: Lens' (GovState era) (PParams era)

  -- | Lens for accessing the future protocol parameters.
  --
  -- This lens will produce `DefinitePParamsUpdate` whenever we are absolutely sure that
  -- the new PParams will be updated. Which means there will be no chance of a
  -- `DefinitePParamsUpdate` value until we are past the point of no return, which is 2
  -- stability windows before the end of the epoch.
  futurePParamsGovStateL :: Lens' (GovState era) (FuturePParams era)

  obligationGovState :: GovState era -> Obligations

instance Crypto c => EraGov (ShelleyEra c) where
  type GovState (ShelleyEra c) = ShelleyGovState (ShelleyEra c)

  getProposedPPUpdates = Just . sgsCurProposals

  curPParamsGovStateL = curPParamsShelleyGovStateL

  prevPParamsGovStateL = prevPParamsShelleyGovStateL

  futurePParamsGovStateL = futurePParamsShelleyGovStateL

  obligationGovState = const mempty -- No GovState obigations in ShelleyEra

data ShelleyGovState era = ShelleyGovState
  { sgsCurProposals :: !(ProposedPPUpdates era)
  , sgsFutureProposals :: !(ProposedPPUpdates era)
  , sgsCurPParams :: !(PParams era)
  , sgsPrevPParams :: !(PParams era)
  , sgsFuturePParams :: FuturePParams era
  -- ^ Prediction of parameter changes that might happen on the epoch boundary. The field
  -- is lazy on purpose, since we truly need to compute this field only towards the end of
  -- the epoch, which is deon by `solidifyFuturePParams`.
  }
  deriving (Generic)

data FuturePParams era
  = NoPParamsUpdate
  | -- | There is no guarantee that these will be the new PParams, no user outside of
    -- ledger should rely on this value to be computed efficiently either and should use
    -- `nextEpochPParams` instead.
    PotentialPParamsUpdate !(PParams era)
  | DefinitePParamsUpdate !(PParams era)
  deriving (Generic)

instance Default (FuturePParams era) where
  def = NoPParamsUpdate

instance ToJSON (PParams era) => ToJSON (FuturePParams era)

-- | Return new PParams only when it is known tha there was an update and it is guaranteed to be applied
maybeFuturePParams :: FuturePParams era -> Maybe (PParams era)
maybeFuturePParams = \case
  DefinitePParamsUpdate pp -> Just pp
  _ -> Nothing

-- | This function is guaranteed to produce `PParams` that will be adopted at the next
-- epoch boundary, whenever this function is applied to the `GovState` that was produced
-- by ledger at any point that is two stability windows before the end of the epoch.
nextEpochPParams :: EraGov era => GovState era -> PParams era
nextEpochPParams govState =
  fromMaybe (govState ^. curPParamsGovStateL) $
    maybeFuturePParams (govState ^. futurePParamsGovStateL)

solidifyFuturePParams :: FuturePParams era -> FuturePParams era
solidifyFuturePParams = \case
  NoPParamsUpdate -> NoPParamsUpdate
  -- Here we convert a potential to a definite update:
  PotentialPParamsUpdate pp -> DefinitePParamsUpdate pp
  DefinitePParamsUpdate pp -> DefinitePParamsUpdate pp

deriving stock instance Eq (PParams era) => Eq (FuturePParams era)
deriving stock instance Show (PParams era) => Show (FuturePParams era)
instance NoThunks (PParams era) => NoThunks (FuturePParams era)
instance (Typeable era, EncCBOR (PParams era)) => EncCBOR (FuturePParams era) where
  encCBOR =
    encode . \case
      NoPParamsUpdate -> Sum NoPParamsUpdate 0
      PotentialPParamsUpdate pp -> Sum PotentialPParamsUpdate 1 !> To pp
      DefinitePParamsUpdate pp -> Sum DefinitePParamsUpdate 2 !> To pp

instance (Typeable era, DecCBOR (PParams era)) => DecCBOR (FuturePParams era) where
  decCBOR = decode . Summands "FuturePParams" $ \case
    0 -> SumD NoPParamsUpdate
    1 -> SumD PotentialPParamsUpdate <! From
    2 -> SumD DefinitePParamsUpdate <! From

instance NFData (PParams era) => NFData (FuturePParams era) where
  rnf = \case
    NoPParamsUpdate -> ()
    PotentialPParamsUpdate pp -> rnf pp
    DefinitePParamsUpdate pp -> rnf pp

proposals :: ShelleyGovState era -> ProposedPPUpdates era
proposals = sgsCurProposals
{-# DEPRECATED proposals "In favor of `sgsCurProposals`" #-}
futureProposals :: ShelleyGovState era -> ProposedPPUpdates era
futureProposals = sgsFutureProposals
{-# DEPRECATED futureProposals "In favor of `sgsFutureProposals`" #-}
sgovPp :: ShelleyGovState era -> PParams era
sgovPp = sgsCurPParams
{-# DEPRECATED sgovPp "In favor of `sgsCurPParams`" #-}
sgovPrevPp :: ShelleyGovState era -> PParams era
sgovPrevPp = sgsPrevPParams
{-# DEPRECATED sgovPrevPp "In favor of `sgsPrevPParams`" #-}

proposalsL :: Lens' (ShelleyGovState era) (ProposedPPUpdates era)
proposalsL = lens sgsCurProposals (\sgov x -> sgov {sgsCurProposals = x})

futureProposalsL :: Lens' (ShelleyGovState era) (ProposedPPUpdates era)
futureProposalsL = lens sgsFutureProposals (\sgov x -> sgov {sgsFutureProposals = x})

curPParamsShelleyGovStateL :: Lens' (ShelleyGovState era) (PParams era)
curPParamsShelleyGovStateL = lens sgsCurPParams (\sps x -> sps {sgsCurPParams = x})

prevPParamsShelleyGovStateL :: Lens' (ShelleyGovState era) (PParams era)
prevPParamsShelleyGovStateL = lens sgsPrevPParams (\sps x -> sps {sgsPrevPParams = x})

futurePParamsShelleyGovStateL :: Lens' (ShelleyGovState era) (FuturePParams era)
futurePParamsShelleyGovStateL =
  lens sgsFuturePParams (\sps x -> sps {sgsFuturePParams = x})

deriving instance
  ( Show (PParamsUpdate era)
  , Show (PParams era)
  ) =>
  Show (ShelleyGovState era)

deriving instance
  ( Eq (PParamsUpdate era)
  , Eq (PParams era)
  ) =>
  Eq (ShelleyGovState era)

instance
  ( NFData (PParamsUpdate era)
  , NFData (PParams era)
  ) =>
  NFData (ShelleyGovState era)

instance
  ( NoThunks (PParamsUpdate era)
  , NoThunks (PParams era)
  ) =>
  NoThunks (ShelleyGovState era)

instance
  ( Era era
  , EncCBOR (PParamsUpdate era)
  , EncCBOR (PParams era)
  ) =>
  EncCBOR (ShelleyGovState era)
  where
  encCBOR (ShelleyGovState ppup fppup pp ppp fpp) =
    encode $
      Rec ShelleyGovState
        !> To ppup
        !> To fppup
        !> To pp
        !> To ppp
        !> To fpp

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  DecShareCBOR (ShelleyGovState era)
  where
  decShareCBOR _ =
    decode $
      RecD ShelleyGovState
        <! From
        <! From
        <! From
        <! From
        <! From

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  DecCBOR (ShelleyGovState era)
  where
  decCBOR = decNoShareCBOR

instance
  ( Era era
  , EncCBOR (PParamsUpdate era)
  , EncCBOR (PParams era)
  ) =>
  ToCBOR (ShelleyGovState era)
  where
  toCBOR = toEraCBOR @era

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  FromCBOR (ShelleyGovState era)
  where
  fromCBOR = fromEraCBOR @era

instance EraPParams era => ToJSON (ShelleyGovState era) where
  toJSON = object . toPPUPStatePairs
  toEncoding = pairs . mconcat . toPPUPStatePairs

toPPUPStatePairs :: (KeyValue e a, EraPParams era) => ShelleyGovState era -> [a]
toPPUPStatePairs ShelleyGovState {..} =
  [ "proposals" .= sgsCurProposals
  , "futureProposals" .= sgsFutureProposals
  , "curPParams" .= sgsCurPParams
  , "prevPParams" .= sgsPrevPParams
  ]

instance EraPParams era => Default (ShelleyGovState era) where
  def = emptyShelleyGovState

emptyShelleyGovState :: EraPParams era => ShelleyGovState era
emptyShelleyGovState =
  ShelleyGovState
    emptyPPPUpdates
    emptyPPPUpdates
    emptyPParams
    emptyPParams
    NoPParamsUpdate
