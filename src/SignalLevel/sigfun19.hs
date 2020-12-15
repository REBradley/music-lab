{-# LANGUAGE Arrows #-}

module SignalLevel.SigFun19 where

import Euterpea

import Rhythm
import RhythmSpecs as RSpecs

---------------------
-- Writing to File --
---------------------

type ExerciseNum = String
type PageNum = String

writeExercise,writeExerciseNorm :: (Clock c, AudioSample b) =>
  String -> ExerciseNum -> Double -> SigFun c () b -> IO ()
writeExercise name num dur sf =
  outFile
    ("/Users/rbradley/Desktop/hsomex19/exercises/" 
    ++ num ++ "/" ++ name ++ ".wav") dur sf

writeExerciseNorm name num dur sf =
  outFileNorm
    ("/Users/rbradley/Desktop/hsomex19/exercises/" 
    ++ num ++ "/" ++ name ++ "_norm.wav") dur sf

writeExample,writeExampleNorm :: (Clock c, AudioSample b) =>
  String -> PageNum -> Double -> SigFun c () b -> IO ()
writeExample name page dur sf =
  outFile
    ("/Users/rbradley/Desktop/hsomex19/examples/" 
    ++ "pg" ++ page ++ "_" ++ name ++ ".wav") dur sf

writeExampleNorm name page dur sf =
  outFileNorm
    ("/Users/rbradley/Desktop/hsomex19/examples/" 
    ++ "pg" ++ page ++ "_" ++ name ++ "_norm.wav") dur sf

----------------------------------
-- Signals and Generating Sound --
----------------------------------
constA :: Clock c => a -> SigFun c () a
constA = arr . const

data HiRate

instance Clock HiRate where
  rate _ = 88200

type HiResSF a b = SigFun HiRate a b

s1 :: Clock c => SigFun c () Double
s1 = proc () -> do
  s <- oscFixed 440 -< ()
  outA -< s

s2 :: Clock c => SigFun c () Double
s2 = proc () -> do
  osc tab1 0 -< 440

s3 :: Clock c => SigFun c () Double
s3 = proc () -> do
  osc tab2 0 -< 440

s4 :: Clock c => SigFun c () Double
s4 = proc () -> do
  f0 <- oscFixed 440  -< ()
  f1 <- oscFixed 880  -< ()
  f2 <- oscFixed 1320 -< ()
  outA -< (f0 + 0.5*f1 + 0.33*f2)/1.83

s5 :: AudSF () Double
s5 = constA 1000 >>> vibrato 5 20

tab1,tab2 :: Table
tab1 = tableSinesN 4096 [1]
tab2 = tableSinesN 8192 [1.0, 0.5, 0.33]

vibrato :: Clock c => Double -> Double -> SigFun c Double Double
vibrato vfrq dep = proc afrq -> do
  vib <- osc tab1 0 -< vfrq
  aud <- osc tab2 0 -< afrq + vib * dep
  outA -< aud

-----------------
-- Instruments --
-----------------

main = writeExampleNorm "vibrato" "289" dr sf
(dr,sf) = renderSF mel myInstrMap

myInstrMap :: InstrMap (AudSF () Double)
myInstrMap = [(simpleInstr, myInstr)]

simpleInstr :: InstrumentName
simpleInstr = CustomInstrument "Simple Instrument"

myInstr :: Instr (AudSF () Double)
myInstr dur ap vol [vfrq,dep] =
  proc () -> do
    vib <- osc tab1 0 -< vfrq
    aud <- osc tab2 0 -< apToHz ap + vib * dep
    outA -< aud

mel :: Music1
mel =
  let m = line [na1 (c 4 en), na1 (ef 4 en), na1 (f 4 en),
        na2 (af 4 qn), na1 (f 4 en) , na1 (af 4 en),
        na2 (bf 4 qn), na1 (af 4 en), na1 (bf 4 en),
        na1 (c 5 en) , na1 (ef 5 en), na1 (f 5 en),
        na3 (af 5 wn)]
  in instrument simpleInstr m
    where na1 (Prim (Note d p)) = Prim (Note d (p,[Params [0,0]]))
          na2 (Prim (Note d p)) = Prim (Note d (p,[Params [5,10]]))
          na3 (Prim (Note d p)) = Prim (Note d (p,[Params [15,20]]))

---------------
-- Exercises --
---------------

{- Exercise 19.1: © Using the Euterpea function osc, create a simple
 - sinusoidal wave, but using different table sizes and different frequencies
 - and see if you can hear the differences (report on what you hear). Use 
 - outFile to write your results to a file. -}

-- Conclusion: The lower the frequency of the wave, the more you hear a
-- "fuzziness" around the sound you are supposed to be hearing. This happens at
-- all table sizes, but the bigger the table size the more this unwanted effect
-- is lessened. Higher sample rates also lessen this effect.

write19_1 :: IO ()
write19_1 = sequence_ write
  where write = [ nameAndWrite (name frq size) ((fSF >>> oSF) :: Mono HiRate) 
                   | (frq, fSF) <- freqs, 
                     (size, oSF) <- oscSFs]
        name f s = (show f ++ "_" ++ show s) 

nameAndWrite nm sf = writeExerciseNorm nm "19_1" 5 sf

freqs :: Clock c => [(AbsPitch, SigFun c () Double)]
freqs = zip aps (map (constA . apToHz) aps)
  where aps = [26,62,98]

oscSFs :: Clock c => [(Int, SigFun c Double Double)]
oscSFs = zip tsizes (map (flip osc $ 0) tables)
  where tables = map (flip tableSinesN $ [1]) tsizes
        tsizes = [128,1024,4096]



{- Exercise 19.2: © The vibrato function varies a signal's frequency at a given
 - rate and depth. Define an analogous function tremolo that varies the volume
 - at a given rate and depth. However, in a sense, tremolo is a kind of envelope
 - (infinite in duration), so define it as a signal source with which you can
 - then shape whatever signal you wish. Consider the "depth" to be the
 - fractional change to the volume; that is, a value of 0 wouild result in no
 - tremolo, a value of 0.1 would vary the amplitude from 0.9 to 1.1, and so on.
 - Test your result. -}

tremolo :: Clock c => Double -> Double -> SigFun c () Double
tremolo r d = oscFixed r >>> arr (\x -> x + x * d)

s3trem :: Clock c => SigFun c () Double
s3trem = proc () -> do
  s <- s3 -< ()
  t <- tremolo 1 0.4 -< ()
  outA -< (s * t)

write19_2nm = writeExerciseNorm "tremolo" "19_2" 10 (s3trem :: AudSF () Double)

write19_2 = writeExercise "tremolo" "19_2" 10 (s3trem :: AudSF () Double)



{- Exercise 19.3.1: © Define an ADSR envelope generator (i.e. a signal source)
 - called envADSR, with type:
 -
 - type DPair = (Double, Double)   -- pair of duration and amplitude
 - envADSR :: DPair -> DPair -> DPair -> Double -> AudSF () Double
 -
 - The three DPair arguments are the duration and amplitude of the attack, decay
 - and release "phases", respectively, of the envelope. The sustain phase should
 - hold the last value of the decay phase. The fourth argument is the duration
 - of the entire envelope, and thus the duration of the sustain phase should be
 - that value minus the sum of the durations of the other three phases. 
 - (Hint: Use Euterpea's envLineSeg function.) Test your result. -}

type DPair = (Double, Double)    -- (duration, amplitude)
envADSR :: Clock c => DPair -> DPair -> DPair -> Double -> SigFun c () Double
envADSR ap dp rp dur = envLineSeg (1.0 : map snd plist) (map fst plist)
  where plist = [ap,dp,sp,rp]
        sp    = (sdur, snd dp)
        sdur  = dur - (fst ap + fst dp + fst rp)

lobass = proc () -> do
  osc tab2 (1/8) -< 50

lobassADSR :: AudSF () Double
lobassADSR = proc () -> do
  s <- lobass -< ()
  env <- envADSR (0.01,1.0) (0.01,0.75) (0.7,0.0) 1 -< ()
  outA -< (s * env)

write19_3_1 =
  writeExercise "adsr" "19_3" 1 lobassADSR



{- Exercise 19.3.2: © Generate a signal that causes significant clipping and
 - listen to the result. Then, implement a limiter and apply it to the signal.
 - Can you hear the difference? Does it sound different than simply scaling the
 - output with outFileNorm? -}

 -- I can't hear a difference between the clipped signal and the signal with my
 -- *primitive* hard limiter applied. However, I do hear a difference when I
 -- apply a mirror limiter, but the result sounds somewhat worse. The mirror
 -- creates what I would call a "denser" distortion.
 --
 -- Needless to say, these sound much different than outFileNorm, which does a
 -- great job at scaling down the signal. It results in a slightly  quieter 
 -- signal. outFileNorm also seems faster.

clipper :: AudSF () Double
clipper = proc () -> do
  c2 <- osc tab2 0 -< apToHz 36 
  g2 <- osc tab2 (1/2) -< apToHz 43
  outA -< (c2 + (0.5 * g2))

limitedBy :: AudSF () Double -> AudSF Double Double -> AudSF () Double
limitedBy sf limiter = sf >>> limiter

clipperHardLimited = (clipper `limitedBy` hardLimiter)
clipperMirrorLimited = (clipper `limitedBy` mirrorLimiter)
clipperScaleHardLimited = (clipper `limitedBy` hardScaleLimiter)

hardLimiter,mirrorLimiter,hardScaleLimiter :: AudSF Double Double
hardLimiter = arr (\x -> if abs x > 1 then (if x > 1 
                                              then 1
                                              else -1)
                                      else x)

mirrorLimiter = arr (\x -> if abs x > 1.0 then (if x > 1 
                                                   then 1 - (x - 1) 
                                                   else ((-1) + ((-1)-x)))
                                          else x)

hardScaleLimiter = 
  arr (\x -> if abs x > 0.9 then if x > 0.9 
                                   then 0.9 + (x - 0.9) * (0.1/0.6) 
                                   else (-0.9) + (x - (-0.9)) * (0.1/0.6) 
                            else x)

write19_3_2 =
  writeExercise "clipping" "19_3" 5 clipper

write19_3_2_nm =
  writeExerciseNorm "clipping" "19_3" 5 clipper

write19_3_2_hardlim =
  writeExercise "clipping_hard_lim" "19_3" 5 clipperHardLimited

write19_3_2_mirrorlim =
  writeExercise "clipping_mirror_lim" "19_3" 5 clipperMirrorLimited

write19_3_2_scalelim =
  writeExercise "clipping_scale_lim" "19_3" 5 clipperScaleHardLimited


{- Exercise 19.4: © Define two instruments, each of type 
 - Instr (AudSF () Double). These can be as simple as you like, but each must
 - take at least two Params. Define an InstrMap that uses these, and then use
 - renderSF to "drive" your instruments from a Music1 value. Test your result. 
 - -}

writeLine = writeExercise "808Line" "19_4" durLn sfunLn
(durLn,sfunLn) = renderSF (tempo (2/3) (m1 :=: m2)) roland808

writeBass = writeExercise "808Kick" "19_4" durB sfunB
(durB,sfunB) = renderSF (tempo (2/3) m1) roland808

writeSnare = writeExercise "808Snare" "19_4" durS sfunS
(durS,sfunS) = renderSF (tempo (1/1) m2) roland808

roland808 :: InstrMap (HiResSF () Double)
roland808 = [(kick,kick808),(snare,snare808)]

kick :: InstrumentName
kick = CustomInstrument "Kick808"

kick808 :: Instr (HiResSF () Double)
kick808 dur ap vol [dfactor,pchng] = 
  proc () -> do
    let f = apToHz ap
    penv <- envExpon 0.5 (0.001 * fromRational dur) 0 -< ()
    bend <- envLineSeg [0,0,1] 
                       [0.6 * fromRational dur, 0.4 * fromRational dur] -< ()
    s    <- osc tab2 0 -< (f + f * penv + pchng * bend)
    aenv <- envADSR (0.01*fromRational dur, 1.0)
                    ((0.24 + dfactor*0.2)*fromRational dur, 0.75) 
                    ((0.75 - dfactor*0.2)*fromRational dur, 0.0)
                    (fromRational dur) -< ()
    outA -< (s * aenv)

m1 :: Music Note1
m1 = instrument kick $
     soundOnDivLine RSpecs.note44{measureTrans = mt} [ku,ku,ku,kd,kd] [1,2,4,5]
     where ku = ((D,1),[Params [0.9,12]])
           km = ((D,1),[Params [0.2,0]]) 
           kd = ((D,1),[Params [0.9,(-12)]]) 
           mt = applyIf odd $ subDivide 2


snare :: InstrumentName
snare = CustomInstrument "Snare808"

snare808 :: Instr (HiResSF () Double)
snare808 dur ap vol [dfactor,vdepth] = 
  proc () -> do
    let af = apToHz . absPitch $ (D,3)
    s1    <- osc tab2 0 -< (af)
    v     <- oscFixed 50 -< ()
    s2    <- sosc -< (apToHz ap + (v * vdepth))
    aenv1 <- envExpon 1 (0.5 * fromRational dur) 0.001 -< ()
    aenv2 <- envExpon 0.5 (0.6 * fromRational dur) (0.1*dfactor) -< ()
    wn    <- noiseWhite 1 -< ()
    outA  -< (s1 * aenv1 + (s2 + wn) * aenv2)

sosc :: HiResSF Double Double
sosc = osc tabsaw 0
  where tabsaw = tableLinear 8192 0 l
        l = (take 4096 $ f (1/8192, 1/4096)) ++ (take 4096 $ f (1/8192,(-1)))
        f = iterate (\(x,y) -> (x, y + 1/4096))

m2 :: Music Note1
m2 = instrument snare $
       soundOnDivLine RSpecs.note44 [s1,s2] [2,4]
     where s1 = ((D,4),[Params [0.1,50]])
           s2 = ((D,1),[Params [0.5,50]]) 
