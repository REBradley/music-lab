module MusicTransformations where

import Euterpea

prefixes :: [a] -> [[a]]
prefixes []     = []
prefixes (x:xs) = let f pf = x : pf
                  in [x] : map f (prefixes xs)

phaseIt :: Dur -> Music a -> Music a
phaseIt factor m = m :=: tempo factor m
