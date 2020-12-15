module SelfSim where 

import Euterpea

-- Exercises Completed:
-- 1[]  2[]  3[]  4[]  5[]  6[]  7[]  8[]  9[]



data Cluster = Cluster SNote [Cluster] 
  deriving Show

type SNote = (Dur,AbsPitch)

selfSim     :: [SNote] -> Cluster
selfSim pat = Cluster (0,0) (map mkCluster pat)
  where mkCluster note = Cluster note (map (mkCluster . addMult note) pat)

addMult                 :: SNote -> SNote -> SNote
addMult (d0,p0) (d1,p1) = (d0*d1,p0+p1)

fringe :: Int -> Cluster -> [SNote]
fringe 0 (Cluster note cls) = [note]
fringe n (Cluster note cls) = concatMap (fringe (n-1)) cls

simToMusic    :: [SNote] -> Music Pitch
simToMusic    = line . map mkNote

mkNote    :: (Dur,AbsPitch) -> Music Pitch
mkNote (d,ap) = note d (pitch ap)

ss pat n tr te = 
  transpose tr $ tempo te $ simToMusic $ fringe n $ selfSim pat

-- Examples --
m0 :: [SNote]
m0 = [(1,2),(1,0),(1,5),(1,7)]
tm0 = instrument Vibraphone (ss m0 4 50 20)

ttm0 = tm0 :=: transpose (12) (retro tm0)

m1 :: [SNote]
m1 = [(1,0),(0.5,0),(0.5,0)]
tm1 = instrument Percussion (ss m1 4 43 2)

m2 :: [SNote]
m2 = [(dqn,0),(qn,4)]
tm2 = ss m2 6 50 (1/50)

m3 :: [SNote]
m3 = [(hn,3),(qn,4),(qn,0),(hn,6)]
tm3 = ss m3 4 50 (1/4)
ttm3 = let l1 = instrument Flute tm3
           l2 = instrument AcousticBass $ 
                  transpose (-9) (retro tm3)
       in l1 :=: l2

m4 :: [SNote]
m4 = [(hn,3),(hn,8),(hn,22),(qn,4),(qn,7),(qn,21), 
      (qn,0),(qn,5),(qn,15),(wn,6),(wn,9),(wn,19)]
tm4 = ss m4 3 50 2


{- EXERCISE 10.2: Note that concat is defined as foldr (++) [], which means that
 - it takes a number of steps proportional to the sum of the lengths of the list
 - being concatenated; we cannot do any better than this. (If foldl were used
 - instead, the number of steps would be proprotional to the number of lists
 - times their average length.)
 -
 - However, fringe is not very efficient, for the following reason: concat is
 - being used over and over again, like this:
 -
 - [concat[concat[..],concat[..],concat[..]]]
 -
 - This causes a number of steps proportional to the depth of the tree times
 - the length of the sub-lists; clearly not optimal. Define a version of fringe
 - that is linear in the total length of the final list. -}



{- EXERCISE 10.1: Experiment with this idea further (original ss function) 
 - using other melodic seeds, exploring different depths of the clusters, and 
 - so on. -}

{- EXERCISE 10.3: Experiment  with the self-similar programs in this chapter.
 - Compose an interesting piece of music through a judicious choice of starting
 - melody, depth of recursion, instrumentation, etc. -}

aryth0 = [(1,0),(0.5,0),(1,0),(0.5,0)]
ssr0 = instrument Percussion (ss aryth0 8 44 4)

aryth1 = [(0.7,0),(0.8,0)]
ssr1 = instrument Percussion (ss aryth1 8 51 1)
ssrr = ssr1 :=: retro ssr1

aryth2 = [(hn,5),(wn,7),(hn,10)]
ssr2 = instrument ChurchOrgan (ss aryth2 5 30 1)
sssorg = ssr2 :=: retro ssr2

amel :: [SNote]
amel = [(0.9,5),(0.7,9),(0.6,13)]
ssMel = instrument Vibraphone (ss amel 6 40 hn)

composition1 = ssMel :=: ssr2


{-
EXERCISE 10.4: Devise an implememtation of a Cluster that plays multiple 
levels of the Cluster in parallel. Try to get the levels to align 
properly in time so that each level has the same duration. You may choose
to play all the levels up to a certain depth in parallel or levels within
a certain range, say levels 3 through 5.-}


