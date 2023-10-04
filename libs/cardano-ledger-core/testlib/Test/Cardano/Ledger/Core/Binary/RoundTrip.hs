{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Core.Binary.RoundTrip (
  -- * Spec
  roundTripEraSpec,
  roundTripAnnEraSpec,
  roundTripEraTypeSpec,
  roundTripAnnEraTypeSpec,
  roundTripShareEraSpec,
  roundTripShareEraTypeSpec,

  -- * Expectation
  roundTripEraExpectation,
  roundTripEraTypeExpectation,
  roundTripAnnEraExpectation,
  roundTripAnnEraTypeExpectation,
  roundTripShareEraExpectation,
  roundTripShareEraTypeExpectation,
  roundTripCoreEraTypesSpec,
) where

import Cardano.Ledger.Binary
import Cardano.Ledger.CertState
import Cardano.Ledger.Compactible
import Cardano.Ledger.Core
import Cardano.Ledger.EpochBoundary
import Cardano.Ledger.Keys.Bootstrap
import Cardano.Ledger.UTxO
import Data.Typeable
import Test.Cardano.Ledger.Binary.RoundTrip
import Test.Cardano.Ledger.Common
import Test.Cardano.Ledger.Core.Arbitrary ()

-- | QuickCheck property spec that uses `roundTripEraExpectation`
roundTripEraSpec ::
  forall era t.
  (Era era, Show t, Eq t, EncCBOR t, DecCBOR t, Arbitrary t) =>
  Spec
roundTripEraSpec =
  prop (show (typeRep $ Proxy @t)) $ roundTripEraExpectation @era @t

-- | Roundtrip CBOR testing for types and type families that implement
-- EncCBOR/DecCBOR. Requires TypeApplication of an @@era@
roundTripEraExpectation ::
  forall era t.
  (Era era, Show t, Eq t, EncCBOR t, DecCBOR t) =>
  t ->
  Expectation
roundTripEraExpectation =
  roundTripCborRangeExpectation (eraProtVerLow @era) (eraProtVerHigh @era)

-- | QuickCheck property spec that uses `roundTripAnnEraExpectation`
roundTripAnnEraSpec ::
  forall era t.
  (Era era, Show t, Eq t, ToCBOR t, DecCBOR (Annotator t), Arbitrary t) =>
  Spec
roundTripAnnEraSpec =
  prop (show (typeRep $ Proxy @t)) $ roundTripAnnEraExpectation @era @t

-- | Similar to `roundTripEraExpectation`, but for Annotator decoders. Note the
-- constraint `ToCBOR` vs `EncCBOR`, this is due to the requirement for memoized types
-- to be already fully encoded.
roundTripAnnEraExpectation ::
  forall era t.
  (Era era, Show t, Eq t, ToCBOR t, DecCBOR (Annotator t)) =>
  t ->
  Expectation
roundTripAnnEraExpectation =
  roundTripAnnRangeExpectation (eraProtVerLow @era) (eraProtVerHigh @era)

-- | QuickCheck property spec that uses `roundTripEraTypeExpectation`
roundTripEraTypeSpec ::
  forall era t.
  (Era era, Show (t era), Eq (t era), EncCBOR (t era), DecCBOR (t era), Arbitrary (t era)) =>
  Spec
roundTripEraTypeSpec =
  prop (show (typeRep $ Proxy @(t era))) $ roundTripEraTypeExpectation @era @t

-- | Roundtrip CBOR testing for types that implement EncCBOR/DecCBOR. Unlike
-- `roundTripEraExpectation`, this function can't be used with type families, but the
-- types of this function are unambiguous.
roundTripEraTypeExpectation ::
  forall era t.
  (Era era, Show (t era), Eq (t era), EncCBOR (t era), DecCBOR (t era)) =>
  t era ->
  Expectation
roundTripEraTypeExpectation = roundTripEraExpectation @era @(t era)

-- | QuickCheck property spec that uses `roundTripAnnEraTypeExpectation`
roundTripAnnEraTypeSpec ::
  forall era t.
  ( Era era
  , Show (t era)
  , Eq (t era)
  , ToCBOR (t era)
  , DecCBOR (Annotator (t era))
  , Arbitrary (t era)
  ) =>
  Spec
roundTripAnnEraTypeSpec =
  prop (show (typeRep $ Proxy @(t era))) $ roundTripAnnEraTypeExpectation @era @t

-- | Same as `roundTripAnnEraExpectation`, but is not suitable for type families.
roundTripAnnEraTypeExpectation ::
  forall era t.
  ( Era era
  , Show (t era)
  , Eq (t era)
  , ToCBOR (t era)
  , DecCBOR (Annotator (t era))
  ) =>
  t era ->
  Expectation
roundTripAnnEraTypeExpectation = roundTripAnnEraExpectation @era @(t era)

-- | QuickCheck property spec that uses `roundTripShareEraExpectation`
roundTripShareEraSpec ::
  forall era t.
  (Era era, Show t, Eq t, EncCBOR t, DecShareCBOR t, Arbitrary t) =>
  Spec
roundTripShareEraSpec =
  prop (show (typeRep $ Proxy @t)) $ roundTripShareEraExpectation @era @t

-- | Roundtrip CBOR testing for types and type families that implement
-- EncCBOR/DecShareCBOR. Requires TypeApplication of an @@era@
roundTripShareEraExpectation ::
  forall era t.
  (Era era, Show t, Eq t, EncCBOR t, DecShareCBOR t) =>
  t ->
  Expectation
roundTripShareEraExpectation =
  roundTripRangeExpectation
    (mkTrip encCBOR decNoShareCBOR)
    (eraProtVerLow @era)
    (eraProtVerHigh @era)

-- | QuickCheck property spec that uses `roundTripShareEraTypeExpectation`
roundTripShareEraTypeSpec ::
  forall era t.
  (Era era, Show (t era), Eq (t era), EncCBOR (t era), DecShareCBOR (t era), Arbitrary (t era)) =>
  Spec
roundTripShareEraTypeSpec =
  prop (show (typeRep $ Proxy @(t era))) $ roundTripShareEraTypeExpectation @era @t

-- | Roundtrip CBOR testing for types that implement EncCBOR/DecShareCBOR. Unlike
-- `roundTripShareEraExpectation`, this function can't be used with type families, but the
-- types of this function are unambiguous.
roundTripShareEraTypeExpectation ::
  forall era t.
  (Era era, Show (t era), Eq (t era), EncCBOR (t era), DecShareCBOR (t era)) =>
  t era ->
  Expectation
roundTripShareEraTypeExpectation = roundTripShareEraExpectation @era @(t era)

-- | CBOR RoundTrip spec for all the core types and type families that are parametrized on era.
roundTripCoreEraTypesSpec ::
  forall era.
  ( EraTx era
  , Arbitrary (Tx era)
  , Arbitrary (TxBody era)
  , Arbitrary (TxOut era)
  , Arbitrary (TxCert era)
  , Arbitrary (TxWits era)
  , Arbitrary (TxAuxData era)
  , Arbitrary (Value era)
  , Arbitrary (CompactForm (Value era))
  , Arbitrary (Script era)
  , Arbitrary (PParams era)
  , Arbitrary (PParamsUpdate era)
  ) =>
  Spec
roundTripCoreEraTypesSpec = do
  describe "Core Type Families" $ do
    roundTripEraSpec @era @(Value era)
    roundTripEraSpec @era @(CompactForm (Value era))
    roundTripEraSpec @era @(TxOut era)
    roundTripEraSpec @era @(TxCert era)
    roundTripEraSpec @era @(PParams era)
    roundTripEraSpec @era @(PParamsUpdate era)
    roundTripAnnEraSpec @era @(BootstrapWitness (EraCrypto era))
    roundTripAnnEraSpec @era @(Script era)
    roundTripAnnEraSpec @era @(TxAuxData era)
    roundTripAnnEraSpec @era @(TxWits era)
    roundTripAnnEraSpec @era @(TxBody era)
    roundTripAnnEraSpec @era @(Tx era)
  describe "Core State Types" $ do
    roundTripShareEraSpec @era @(SnapShots (EraCrypto era))
    roundTripShareEraTypeSpec @era @DState
    roundTripShareEraTypeSpec @era @PState
    roundTripShareEraSpec @era @(CommitteeState (EraCrypto era))
    roundTripShareEraTypeSpec @era @VState
    roundTripShareEraTypeSpec @era @CertState
    roundTripShareEraTypeSpec @era @UTxO
