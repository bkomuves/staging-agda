
module Aux.Lens where

--------------------------------------------------------------------------------

import Control.Monad.State.Strict

--------------------------------------------------------------------------------

data Lens a b = MkLens 
  { getter :: a -> b 
  , setter :: b -> a -> a 
  }

modifier :: Lens a b -> (b -> b) -> a -> a
modifier lens f x = setter lens (f (getter lens x)) x

--------------------------------------------------------------------------------
-- state monad

getVia :: Monad m => Lens s a -> StateT s m a
getVia lens = getter lens <$> get

setVia :: Monad m => Lens s a -> a -> StateT s m ()
setVia lens x = modify (setter lens x)

modifyVia :: Monad m => Lens s a -> (a -> a) -> StateT s m ()
modifyVia lens f = modify (modifier lens f)

--------------------------------------------------------------------------------
