module Midi where

import Euterpea

class ToMusic1 a where
  toMusic1 :: Music a -> Music1

instance ToMusic1 Pitch where 
  toMusic1 = mMap (\p -> (p,[]))

instance ToMusic1 (Pitch, Volume) where 
  toMusic1 = mMap ( \(p,v) -> (p,[Volume v]) )

instance ToMusic1 (Note1) where 
  toMusic1 = id


data MEvent = MEvent {
  eTime    :: PTime, 
  eInst    :: InstrumentName, 
  ePitch   :: AbsPitch, 
  eDur     :: DurT,
  eVol     :: Volume, 
  eParams :: [Double]}
  deriving (Show,Eq,Ord)

type Performance = [MEvent]
type PTime = Rational
type DurT = Rational
