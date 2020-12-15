module PHoF where
import Euterpea

f1 :: Int -> [Pitch] -> [Pitch]
f1 _ [] = []
f1 0 xs = xs
f1 i xs = map (trans i) xs

f2 :: [Dur] -> [Music a]
f2 [] = []
f2 ds = map rest ds

f3 :: [Music Pitch] -> [Music Pitch]
f3 ps = let f (Prim(Note d p)) = (note (d/2) p) :+: rest (d/2)
        in map f ps

{--
SHOW flip (flip f) = f

flip (flip f) x y = (flip f) y x
                  = flip f y x
                  = f x y
                  = f
--}

--DEFINE the type of ys in:

xs = [1,2,3] :: [Integer]
ys = map (+) xs

--ys :: [Integer -> Integer]


simple x y z = x * (y + z)

applyEach          :: [a -> b] -> a -> [b]
applyEach [] x     = []
applyEach (f:fs) x = f x : applyEach fs x


applyAll          :: [a -> a] -> a -> a
applyAll [] v     = v
applyAll (f:fs) v = f( applyAll fs v)




{-- 
 - WHICH FUNCTION IS MOST EFFICIENT? WHY?
 -
 - appendr, appendl :: [[a]] -> [a]
 - appendr = foldr (flip (++)) []
 - appendl = foldl (flip (++)) []
 -
 - appendr (xs:xss) = xs (flip (++)) foldr (flip (++)) [] xss
 -                  = (foldr (flip (++)) [] xss) ++ xs
 -
 - appendr [xs1,...,xsn] = (foldr (flip (++)) [] [xs2,...,xsn]) ++ xs1
 -                       = ([] ++ (xsn ++ ... ++ xs3) ++ xs2) ++ xs1        
 -
 -
 - appendl (xs:xss) = foldl (flip (++)) ([] (flip (++)) xs) xss
 -                  = foldl (flip (++)) (xs (++) []) xss
 - 
 - appendl [xs1,...,xsn] = foldl (flip (++)) (xs1 ++ []) [xs2,...,xsn]
 -                       = (xsn ++ ... (xs2 ++ (xs1 ++ [])))
 -
 -
 - APPENDL IS MORE EFFICIENT BECAUSE IT DOES NOT "GO THROUGH LISTS AGAIN",
 - MEANING THAT THE COST OF COMPUTING IT IS PROPORTIONAL TO THE LENGTH OF ALL
 - THE LISTS. MEANWHILE, APPENDR CONTINUES TO GO THROUGH LISTS IT "ACCUMULATES",
 - AND ENDS UP COSTING MUCH MORE (PROPORTIONAL TO N^2). THE COST OF APPENDL IS
 - LINEAR.
 -
 -
 - --}


length' :: [a] -> Int
length' xs = let f _ = 1
             in sum (map f xs)



doubleEach xs = map (*2) xs

pairAndOne xs = let pairUp n = (n, n+1)
                in map pairUp xs

addEachPair xs = let addPair (x,y) = x+y
                 in map addPair xs

addPairsPointwise xs = let takeFst (x,_) = x
                           takeSnd (_,y) = y
                       in (sum (map takeFst xs), sum (map takeSnd xs))

fuse :: [Dur] -> [Dur -> Music a] -> [Music a]
fuse [] []         = []
fuse [] fs         = error "fuse: lists unequal length"
fuse ds []         = error "fuse: lists unequal length"
fuse (d:ds) (f:fs) = f d : fuse ds fs




--1 RECURSIVE AND 1 NON-RECURSIVE DEFINITION OF MAXABSPITCH, MINABSPITCH


(>!!) :: AbsPitch -> AbsPitch -> AbsPitch
ap1 >!! ap2 = if ap1 > ap2 then ap1 else ap2

(<!!) :: AbsPitch -> AbsPitch -> AbsPitch
ap1 <!! ap2 = if ap1 < ap2 then ap1 else ap2


maxAbsPitch'     :: [AbsPitch] -> AbsPitch
maxAbsPitch' []  = error "maxAbsPitch: empty list"
maxAbsPitch' aps = let f [x]    = x
                       f (x:xs) = x >!! f xs
                   in f aps


minAbsPitch'     :: [AbsPitch] -> AbsPitch
minAbsPitch' []  = error "minAbsPitch: empty list"
minAbsPitch' aps = let f [x]    = x
                       f (x:xs) = x <!! f xs
                   in f aps


maxAbsPitch :: [AbsPitch] -> AbsPitch
maxAbsPitch ps = foldr1 (>!!) ps

minAbsPitch :: [AbsPitch] -> AbsPitch
minAbsPitch ps = foldl1 (<!!) ps


{-- EXERCISE 3.11 Define a function chrom :: Pitch -> Pitch -> Music Pitch such
 - that chrom p1 p2 is a chromatic scale of quarter notes whose first pitch is
 - p1 and last pitch is p2. If p1 > p2, the scale should be descending,
 - otherwise it should be ascending. If p1 == p2, then the scale should contain
 - just one note. Give both recursive and (if possible) non-recursive definitions.
--}


--RECURSIVE
chrom :: Pitch -> Pitch -> Music Pitch
chrom p1 p2 | p1 == p2                  = qNote p2
            | absPitch p1 > absPitch p2 = qNote p1 :+: chrom (trans (-1) p1) p2 
            | absPitch p1 < absPitch p2 = qNote p1 :+: chrom (trans 1 p1) p2
            where qNote = note qn

--NONRECURSIVE
chrom' p1 p2 = foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) incs
  where ap1  = absPitch p1
        ap2  = absPitch p2
        incs = if ap1 <= ap2 then [ap1..ap2] else [ap2,(ap2-1)..ap1]


mkScale          :: Pitch -> [Int] -> Music Pitch
mkScale p []     = note qn p
mkScale p (x:xs) = note qn p :+: (mkScale (trans x p) xs)

mkScale' p ints = foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) pitches
  where pitches = scanl (+) (absPitch p) ints
  


data Mode' = Ionian' | Dorian' | Phrygian' | Lydian'
             | Mixolydian' | Aeolian' | Locrian'


genScale :: Pitch -> Mode' -> Music Pitch
genScale tonic mode = case mode of
                Ionian' ->     mkScale tonic [2,2,1,2,2,2,1]
                Dorian' ->     mkScale tonic [2,1,2,2,2,1,2] 
                Phrygian' ->   mkScale tonic [1,2,2,2,1,2,2]
                Lydian' ->     mkScale tonic [2,2,2,1,2,2,1]
                Mixolydian' -> mkScale tonic [2,2,1,2,2,1,2]
                Aeolian' ->    mkScale tonic [2,1,2,2,1,2,2]
                Locrian' ->    mkScale tonic [1,2,2,1,2,2,2]

{--EXERCISE 3.14 Write the melody of "Frere Jacques" (or "Are You Sleeping?")
 - in Euterpea. Try to make it as succinct as possible. Then, using functions
 - already defined, generate a traditional four-part round, i.e., four identical
 - voices, each delayed successively by two measures. Use a different instrument
 - to realize each voice. --}

jacques :: Music Pitch
jacques = let qNote p     = note qn p; hNote p = note hn p; eNote p = note en p
              repeat l = l :+: l
          in line (map (qNote) [(C,4),(D,4),(E,4),(C,4),(C,4),(D,4),(E,4),(C,4)])
             :+: repeat (line [qNote (E,4), qNote (F,4), hNote (G,4)])
             :+: repeat (line [eNote (G,4), eNote (A,5), eNote (G,4), eNote (F,4), qNote (D,4), qNote (C,4)])
             :+: repeat ((line [qNote (C,4),rest qn,hNote (C,4)] :=: line [rest qn,qNote (G,3),rest hn]))

jacques0 ::  Music Pitch
jacques0 = instrument TinkleBell jacques


jacques1 ::  Music Pitch
jacques1 = instrument MelodicDrum jacques



jacques2 ::  Music Pitch
jacques2 = instrument HonkyTonkPiano jacques


fourPartRound :: Music Pitch
fourPartRound = chord [jacques, line [bnr,jacques0],line[bnr,bnr,jacques1],line[bnr,bnr,bnr,jacques2]]

{-- EXERCISE 3.15: Freddie the Frog wants to communicate privately with his
 - girlfriend, Francine, by encrypting messages he sends to her. Frog brains are
 - not that large, so they agree on this simple strategy: each character in the
 - text shall be converted to the character "one greater" than it, based on the
 - representation described below (with wrap-around from 255 to 0).
 -
 - Definethe functions encrypt and decrypt that will allow Freddie and Francine
 - to communicate using this strategy. -}


encrypt   :: [Char] -> [Int]
encrypt = map ((+1) . fromEnum)

decrypt   :: [Int] -> [Char]
decrypt = map (toEnum . (subtract 1))




































