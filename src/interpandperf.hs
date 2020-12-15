module InterpAndPerf where 
import Euterpea
import Interlude
import HSoM
import Data.List (sortBy)

-- never had to insert insert {-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-} --


myPMap             :: PlayerName -> Player Note1 
myPMap "NewPlayer" = newPlayer 
myPMap "MyPlayer"  = myPlayer
myPMap "JazzMan"   = jazzMan
myPMap p           = defPMap p

newPlayer :: Player (Pitch,[NoteAttribute])
newPlayer = defPlayer 
  {pName        = "NewPlayer", 
   interpPhrase = defInterpPhrase myPasHandler}


{-EXERCISE 9.1 : Fill in the ... in the definition of myPasHandler according to the 
following strategy: Gradually scale the volume of each event in the performance by a 
factor of 1 through 1 + x using linear interpolation. -}

myPasHandler :: PhraseAttribute -> Performance -> Performance
myPasHandler (Dyn (Crescendo x)) pf@(init:evs) = 
  map (\e -> e {eVol = round (fromIntegral (eVol e) * (factor $ eTime e))}) pf
    where factor t = (1 + x * (t - eTime init)/pDur)
          pDur     = foldl (\d e -> d + eDur e) 0 pf
myPasHandler pa                  pf = defPasHandler pa pf 



{-EXERCISE 9.2: Choose some of the other attributes and provide interpretations
 - for them.-}
{-EXERCISE 9.3: Define a player myPlayer that appropriately handles the Pedal
 - articulation and both the ArpeggioUp and ArpeggioDown ornamentations. You
 - should define myPlayer as a derivative of defPlayer or new Player.-}
{-EXERCISE 9.5: Implement the ornamentation DiatonicTrans, which is intended to
 - be a "diatonic transposition" within a particular key. The argument to
 - DiatonicTrans is an integer representing the number of scale degrees to do
 - the transposition.-}

myPlayer :: Player (Pitch,[NoteAttribute])
myPlayer = defPlayer 
  {pName = "MyPlayer", 
   interpPhrase = customInterpPhrase}


customInterpPhrase :: PhraseFun a
customInterpPhrase pm c [] m = perf pm c m
customInterpPhrase pm 
  c@Context {cTime = t,cPlayer = pl,cInst = i, 
             cDur = dt,cPch = k,cVol = v,cKey = (pc,mo)}
  (pa:pas) m = 
    let pfd@(pf,dur) = customInterpPhrase pm c pas m
        hold         = customInterpPhrase pm c (Art(Legato (3/2)):pas) m
        mark         = customInterpPhrase pm c (Dyn(Accent (3/2)):pas) m
        pedalTone    = (\e -> 
                         e {eTime = t,
                            ePitch = absPitch (pc,snd(pitch(ePitch e)) - 1),
                            eDur = dur})
        minP         = foldr1 (\e1 e2 -> if ePitch e1 > ePitch e2 then e2 else e1) pf
        trill        = let upd (e@MEvent {ePitch = p, eDur = d,eTime = t}) =
                             let interval = semitones e
                                 e'       = e {eDur = d/3}
                                 e''      = e' {ePitch = p + interval,eTime = t + d/3}
                                 e'''     = e' {eTime = t + 2*d/3}
                             in [e', e'', e''']
                        in concatMap upd
        semitones e = 
          [tone | (pcls,tone) <- scale pc mo,fst(pitch(ePitch e)) == pcls] !! 0

        arpeggiate f []  = []
        arpeggiate f ps = addtime $ sortBy f ps
        addtime [] = []
        addtime (p:ps) = 
          let plusTime = map (\e@MEvent {eTime = t,eDur = d} -> 
                           e {eTime = t + eDur p}) ps
          in p : (addtime plusTime)
        brkcord f  = concatMap (\p -> if length p >= 3 then arpeggiate f p else p)
        simult []  = []
        simult (p:ps) = (p : filter (\e -> eTime e == (eTime p)) ps) : simult ps
    in case pa of
      Dyn (Crescendo x) -> (myPasHandler pa pf,dur)
      Dyn (Accent x)    -> 
        (map (\e -> e {eVol = round(x * fromIntegral(eVol e))}) pf, dur)
      Art (Legato x)    -> (map (\e -> e {eDur = x * eDur e}) pf, dur)
      Art Tenuto        -> hold
      Art Marcato       -> mark
      Art Pedal         -> (pedalTone minP : pf,dur)
      Orn Trill         -> (trill pf,dur)
      Orn ArpeggioUp    -> 
        (brkcord (\e1 e2 -> compare (ePitch e1) (ePitch e2)) $ simult pf,dur)
      Orn ArpeggioDown  -> 
        (brkcord (\e1 e2 -> flip compare (ePitch e1) (ePitch e2)) $ simult pf,dur)
      Orn (DiatonicTrans i) -> 
        let trans1 e = e { ePitch = ePitch e + semitones e}
        in ([applyN i trans1 e | e <- pf],dur)
      _                 -> pfd

scale :: PitchClass -> Mode -> [(PitchClass,AbsPitch)]
scale t m = 
  let keys            = [C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B]
      fromTonic       = dropWhile (/=t) keys ++ takeWhile (/= t) keys
      withKeys steps  = zip [fromTonic !! n | n <- scanl (+) 0 steps] steps
  in case m of 
    Major -> withKeys [2,2,1,2,2,2,1]
    Minor -> withKeys [2,1,2,2,1,2,2]

applyN :: Int -> (a -> a) -> a -> a
applyN 1 f x = f x
applyN n f x = applyN (n-1) f (f x)


{-EXERCISE 9.4: Define a player jazzMan that plays a melody using a jazz "swing"
 - feel. Since there are different kinds and degrees of swing, we can be more
 - specific as follows: whenever there is a sequence of two eighth notes, they
 - should be interpreted instead as a quarter note followed by an eighth note,
 - but with tempo 3/2. So in essence, the first note is lengthened, and the
 - second note is shortened, so that the first note is twice as long as the
 - second, but they still take up the same amount of overall time. -}

enseq = c 4 en :+: e 4 en :+: c 4 en :+: e 4 en

jazzMan = defPlayer {playNote = jazzNote}

jazzNote :: Context Note1 -> Dur -> Note1 -> Performance
jazzNote 
  c@Context {cTime = t,cPlayer = pl,cInst = i, 
             cDur = dt,cPch = k,cVol = v,cKey = (pc,mo)} d (p,nas) = 
   let swing    = if or [t == (dt*qn)*i | i <- [0 .. 20]] then downbeat else upbeat
       upbeat   = (\e -> e {eDur = (eDur e)*(2/3),eTime = eTime e + (eDur e * 1/3)})
       downbeat = (\e -> e {eDur = (eDur e)*(3/2)})
       initEv   = 
         MEvent {eTime = t,eDur = d*dt,eInst = i,
                 eVol = v,ePitch = k + absPitch p,eParams=[]}
   in [swing initEv] 
  



