{-# LANGUAGE ExistentialQuantification #-}

module Compose where

import Euterpea


---------------------
-- Line -> Section --
---------------------

data Line = forall a . ToMusic1 a => Line (Music a)

layer :: [Line] -> Music Note1
layer = foldr ((:=:) . toM) (rest 0)

toM :: Line -> Music Note1
toM (Line m) = toMusic1 m


------------------------
-- Transforming Lines --
------------------------

transitionWith :: Music a -> Music a -> Music a
transitionWith m m' = cut (dur m - dur m') m :+: m'

layerWith :: Music a -> Music a -> Music a
layerWith m m' = m :=: cut (dur m) m'

