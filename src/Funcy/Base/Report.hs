{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Funcy.Base.Report where

import Control.Monad.Signatures ( Listen, Pass )
import Control.Monad.Trans ( MonadTrans(..) )
import Control.Monad.Identity ( Identity )
import Control.Monad.Reader ( MonadReader(..) )
import Control.Monad.Writer ( MonadWriter(..) )
import Control.Monad.State ( MonadState(..) )
import qualified Control.Monad.Trans.Reader as Reader
import qualified Control.Monad.Trans.Writer as Writer
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.RWS as RWS
import qualified Control.Monad.Trans.Identity as Identity

-- |Class for report monad
class (Monad m) => MonadReport e m | m -> e where
  -- |Report error to be stacked
  reportError :: e -> m ()
  -- |Throw errors, halting execution
  throwErrors :: [e] -> m a
  -- |Handle accumulated error if exists.
  -- Otherwise simply passes the report down.
  handleError :: m a -> ([e] -> m a) -> m a

newtype ReportT e m a = ReportT {
  runReportT :: m (Maybe a, [e])
}

type Report e = ReportT e Identity

-- |Maps both the value and accumulated error using given function.
mapReportT :: (m (Maybe a, [e]) -> n (Maybe b, [e'])) -> ReportT e m a -> ReportT e' n b
mapReportT f = ReportT . f . runReportT

-- |Lift a listen operation to the new monad.
liftListen :: Monad m => Listen w m (Maybe a, [e]) -> Listen w (ReportT e m) a
liftListen listen = mapReportT $ \m -> do
  ((a, e), w) <- listen m
  return $! (fmap (, w) a, e)

liftPass :: Monad m => Pass w m (Maybe a, [e]) -> Pass w (ReportT e m) a
liftPass pass = mapReportT $ \m -> pass $ do
  (a, e) <- m
  return $! case a of
    Nothing -> ((Nothing, e), id)
    Just (b, f) -> ((Just b, e), f)

-- |Converts reported errors.
withReportT :: (Functor m) => (e -> e') -> ReportT e m a -> ReportT e' m a
withReportT f = mapReportT $ fmap . fmap . fmap $ f

instance Functor m => Functor (ReportT e m) where
  fmap f (ReportT v) = ReportT $ fmap (fmap' f) v where
    fmap' f (x, err) = (fmap f x, err)

instance Applicative m => Applicative (ReportT e m) where
  pure x = ReportT $ pure (pure x, [])
  ReportT f <*> ReportT v = ReportT (ap' <$> f <*> v) where
    ap' = undefined

instance Monad m => Monad (ReportT e m) where
  ReportT v >>= f = ReportT $ do
    (x, err) <- v
    case x of
      Nothing -> pure (Nothing, err)
      Just x' -> do
        (res, err') <- runReportT $ f x'
        pure (res, err <> err')

instance MonadTrans (ReportT e) where
  lift = ReportT . fmap ((, []) . pure)

instance Monad m => MonadReport e (ReportT e m) where
  reportError err = ReportT $ pure (Just (), [err])
  throwErrors errs = ReportT $ pure (Nothing, errs)
  handleError report handler = ReportT $ do
    (_, errs) <- runReportT report
    runReportT $ if null errs then report else handler errs

instance MonadReader r m => MonadReader r (ReportT e m) where
  ask = lift ask
  local = mapReportT . local
  reader = lift . reader

instance MonadWriter w m => MonadWriter w (ReportT e m) where
  writer = lift . writer
  tell = lift . tell
  listen = liftListen listen
  pass = liftPass pass

instance MonadState s m => MonadState s (ReportT e m) where
  get = lift get
  put = lift . put
  state = lift . state

-- Undecidable Instances here simply because it can't find
instance MonadReport e m => MonadReport e (Reader.ReaderT r m) where
  reportError = lift . reportError
  throwErrors = lift . throwErrors
  handleError = Reader.liftCatch handleError

instance (Monoid w, MonadReport e m) => MonadReport e (Writer.WriterT w m) where
  reportError = lift . reportError
  throwErrors = lift . throwErrors
  handleError = Writer.liftCatch handleError

instance MonadReport e m => MonadReport e (State.StateT s m) where
  reportError = lift . reportError
  throwErrors = lift . throwErrors
  handleError = State.liftCatch handleError

instance (Monoid w, MonadReport e m) => MonadReport e (RWS.RWST r w s m) where
  reportError = lift . reportError
  throwErrors = lift . throwErrors
  handleError = RWS.liftCatch handleError

instance MonadReport e m => MonadReport e (Identity.IdentityT m) where
  reportError = lift . reportError
  throwErrors = lift . throwErrors
  handleError = Identity.liftCatch handleError

