module ZayBeats where

import Euterpea

hats = forever (perc ClosedHiHat dsn)

clap = forever (perc HandClap qn :+: rest dhn)

bass = times 2 $
       (times 3 $ perc BassDrum1 en :+: rest en) :+:
       rest en :+: perc BassDrum1 en :+: 
       rest hn :+: (times 3 $ perc BassDrum1 en :+: rest en) :+:
       rest tn :+: perc BassDrum1 en :+: rest en :+: perc BassDrum1 en :+: rest en

snare = perc SideStick qn :+: perc SideStick qn :+: perc SideStick qn :+:
        (times 2 $ perc SideStick dsn :+: perc SideStick dsn :+: rest en)
