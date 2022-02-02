{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Data.Word
import Data.Function
import Data.Functor
import Data.Maybe
import Data.Foldable
import Data.Char
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Debug.Trace

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Codec.Base64 as B64

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text

import qualified Network.DNS as DNS
import Network.DNS (Labels(..),SRV(..))

import Conduit
import Data.Conduit
import qualified Data.Conduit.Combinators as C
import Data.Conduit.Network
import Data.Conduit.Network.TLS
import Network.Connection

import Text.XML.Unresolved
import Text.XML.Stream.Parse as X
import Text.XML.Stream.Render as X (renderBytes)
import Data.XML.Types

import Xmpp

resolveSRV :: Text -> IO (DNS.Name,Int)
resolveSRV domain = do
  let service = "_xmpp-client" -- xmpp-server for S2S
      proto = "_tcp"
      Just nameLabels = DNS.toLabels (DNS.Name (Text.encodeUtf8 domain)) -- origin domain [TLS-CERTS]
  ttlServs <- DNS.querySRV (DNS.fromLabels $ service :.: proto :.: nameLabels)
  traceShowM ttlServs
  case ttlServs of
    [(_,srvTarget -> DNS.Name ".")] -> empty
    -- TODO actually follow DNS-SRV rules (XMPP 3.2.1.4)
    ((_,SRV{srvTarget,srvPort}):_) -> pure (srvTarget,fromIntegral srvPort)

resolve :: Text -> IO (DNS.Name,Int)
resolve domain = do
  -- preferred: DNS-SRV
  resolveSRV domain

tlsSink :: ConduitT Event Void IO ()
tlsSink = do
  let eoFeatures (EventEndElement Name{nameLocalName = "features"}) = True
      eoFeatures _ = False
      tlsResponse (EventEndElement Name{nameNamespace = Just "urn:ietf:params:xml:ns:xmpp-tls"}) = True
      tlsResponse _ = False
  C.dropWhile (not . eoFeatures)
  C.drop 1
  fix $ \loop -> do
    Just (EventEndElement name) <- C.find tlsResponse
    case nameLocalName name of
      "failure" -> 
        liftIO $ ioError (userError $ "Server rejected startTls: " ++ show name)
      "proceed" -> pure ()
      _ -> loop

-- TODO make TLS optional (with warning)
withTLS :: (DNS.Name,Int) -> Text -> (ConduitT ByteString ByteString IO ())
        -> IO ()
withTLS (DNS.Name dest,port) domain action = do
  let config = (tlsClientConfig port dest) { tlsClientTLSSettings = def { settingDisableCertificateValidation = True } }
  runTLSClientStartTLS config $ \(appData,startTLS) -> do
    (openStream domain *> startTls) `connect` appSink appData
    proceed <- runConduit $ appSource appData .| parseBytes def .| tlsSink
    startTLS $ \_ -> runConduit $ do
      appSource appData .| action .| appSink appData
      traceM "end of conduit"

openStream :: PrimMonad m => Text -> ConduitT i ByteString m ()
openStream domain = do
  yield "<?xml version='1.0'?>"
  yield (EventBeginElement streamTag
           [ ("to"      ,[ContentText domain])
           , ("version" ,[ContentText "1.0"])
           , ("xml:lang",[ContentText "en"])
           , ("xmlns"   ,[ContentText "jabber:client"]) ])
    .| X.renderBytes def

emitSaslPlain :: PrimMonad m => Text -> Text
              -> ConduitT a ByteString m ()
emitSaslPlain userName pwd = do
  let base64 = B64.encode $ Text.encodeUtf8 ("\0" <> userName <> "\0" <> pwd)
  flip fuse (X.renderBytes def) $ do
    yield $ EventBeginElement authTag [("mechanism",[ContentText "PLAIN"])]
    yield $ EventContent (ContentText base64)
    yield $ EventEndElement authTag

saslPlainSink :: (MonadFail m,MonadIO m) => ConduitT Event o m ()
saslPlainSink = do
  let saslResponse (EventEndElement Name{nameNamespace = Just "urn:ietf:params:xml:ns:xmpp-sasl"}) = True
      saslResponse _ = False
  fix $ \loop -> do
    Just (EventEndElement name) <- C.find saslResponse
    case nameLocalName name of
      "failure" ->
        liftIO $ ioError (userError $ "Server rejected PLAIN auth: "
                                      ++ show name)
      "success" -> pure ()
      _ -> loop

data Feature = FeatureBind
             | FeatureSession
             | FeatureCaps Text Text Text
             | FeatureSm Int
             | FeatureRosterVer
             | FeatureCsi
             | FeatureUnknown ByteString
  deriving (Show,Eq)

dumpAttrs = optionalAttrRaw (Just . traceShowId)

dumpTag :: (PrimMonad m,MonadThrow m) => ConduitT Event c m (Maybe ByteString)
dumpTag = fmap BS.concat . uncurry ($>) <$> (takeAnyTreeContent `fuseUpstream` X.renderBytes def `fuseBoth` sinkList)

features :: (PrimMonad m,MonadThrow m) => ConduitT Event o m (Maybe [Feature])
features = tag' (tagIs featuresTag) ignoreAttrs
             (\_ -> X.many feature)

feature,featureBind,featureSession,featureCaps,featureSm,featureRosterVer,featureCsi,featureUnknown :: (PrimMonad m,MonadThrow m) => ConduitT Event o m (Maybe Feature)
feature = choose [featureBind,featureSession,featureCaps,featureSm,featureRosterVer,featureCsi,featureUnknown]

tagIs :: Name -> NameMatcher Name
tagIs tag = matching (== tag)

featureBind = tag' (tagIs bindTag) (pure ()) $ \_ -> pure FeatureBind

featureSession = tag' sessionTag (pure ())
                   (\_ -> tag' (matching $ (== "optional") . nameLocalName)
                               (pure ()) (\_ -> pure ())
                               *> pure FeatureSession)

whileAttr attrParser = do
  mattr <- attrParser
  case mattr of
    Nothing -> pure []
    Just attr -> (attr :) <$> whileAttr attrParser

featureCaps = tag' capsTag
                (FeatureCaps <$> requireAttr "hash"
                             <*> requireAttr "node"
                             <*> requireAttr "ver")
                pure

featureSm = tag (matching $ (`elem` [Just sm2ns,Just sm3ns]) . nameNamespace) pure $ \n ->
    do
      if maybe False ("2" `Text.isSuffixOf`) (nameNamespace n)
        then pure (FeatureSm 2)
        else pure (FeatureSm 3)
  where sm2ns = "urn:xmpp:sm:2"
        sm3ns = "urn:xmpp:sm:3"

featureRosterVer = tag' rosterVerTag (pure FeatureRosterVer) pure

featureCsi = tag' csiTag (pure FeatureCsi) pure

featureUnknown = fmap (FeatureUnknown . BS.concat) . uncurry ($>) <$> (takeAnyTreeContent `fuseUpstream` X.renderBytes def `fuseBoth` sinkList)

emitBind :: PrimMonad m => Maybe Text -> ConduitT i ByteString m ()
emitBind mres = sourceBind .| X.renderBytes def .| C.map traceShowId where
  sourceBind = do
    yield $ EventBeginElement "iq" [ ("id",[ContentText "tn281v37"])
                                   , ("type",[ContentText "set"]) ]
    yield $ EventBeginElement bindTag []
    traverse_ (\res -> yield $ EventContent (ContentText res)) mres
    yield $ EventEndElement bindTag
    yield $ EventEndElement "iq"
    

recvBind :: MonadThrow m => ConduitT Event ByteString m (Maybe Text)
recvBind = tag' (tagIs iqTag) (attr "id" *> attr "type") $ \case
  Just "result" ->
    force "bind required" $
    tag' (tagIs bindTag) (pure ()) $ \_ ->
    X.force "jid required" $
    tag' (tagIs bindJidTag) (pure ()) $ \_ ->
    content

process :: Text -> Text -> Text -> IO ()
process userName domain password = do
  dest <- resolve domain
  -- TODO follow connection spec XMPP3.1 more closely
  -- TODO XMPP3.2 fallbacks
  -- TODO handle XMPP3.3 reconnection
  -- TODO investigate XMPP3.4 reliability
  withTLS dest domain $ parseBytesPos def .| do
    openStream domain
    -- TODO: implement other SASL
    emitSaslPlain userName password
    C.map snd .| saslPlainSink

    runStream domain

runStream :: (PrimMonad m,MonadThrow m,MonadFail m,MonadIO m) => Text -> ConduitT EventPos ByteString m ()
runStream domain = do
  traceM "Starting client stream"
  openStream domain
  Just (_,EventBeginElement streamOpenTag streamOpenAttrs) <- await
  liftIO $ guard (streamOpenTag == streamTag)
  traceShowM streamOpenAttrs

  fts <- fromMaybe [] <$> (C.map snd .| features)
  traceShowM fts

  when (FeatureBind `elem` fts) $ do
    emitBind (Just "alpha")
    Just jid <- C.map snd .| recvBind
    traceM $ "Bound JID: " ++ Text.unpack jid

  C.map snd .| (fix $ \loop -> (dumpTag >>= traceShowM) *> loop)
  -- exchangeStanzas

main :: IO ()
main = do
  account <- Text.readFile "account"
  password <- Text.readFile "password"
  let (userName,domain) = parseBareJid account
  process userName domain password

parseBareJid :: Text -> (Text,Text)
parseBareJid account = (userName,domain)
  where (userName,rest) = Text.break (== '@') account
        domain = Text.tail rest

startTls :: PrimMonad m => ConduitT i ByteString m ()
startTls = flip fuse (X.renderBytes def) $ do
  yield $ EventBeginElement startTlsTag []
  yield $ EventEndElement startTlsTag

streamTag = "{http://etherx.jabber.org/streams}stream" {namePrefix = Just "stream"}

featuresTag = "{http://etherx.jabber.org/streams}features"
startTlsTag = "{urn:ietf:params:xml:ns:xmpp-tls}starttls"
authTag = "{urn:ietf:params:xml:ns:xmpp-sasl}auth"
bindTag = "{urn:ietf:params:xml:ns:xmpp-bind}bind"
bindJidTag = "{urn:ietf:params:xml:ns:xmpp-bind}jid"
sessionTag = "{urn:ietf:params:xml:ns:xmpp-session}session"
capsTag = "{http://jabber.org/protocol/caps}c"
rosterVerTag = "{urn:xmpp:features:rosterver}ver"
csiTag = "{urn:xmpp:csi:0}csi"

iqTag = "{jabber:client}iq"
