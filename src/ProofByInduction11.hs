module ProofByInduction11 where

import Prelude
import Euterpea
import Data.List (delete)

{- (11.1) From Chapter 3, prove that the original recursive versions of the
 - following functions are equivalent to the versions using map or fold:
 - toPitches, chord, maxPitch, hList. -}

toPitchesr :: [AbsPitch] -> [Pitch]
toPitchesr [] = []
toPitchesr (a:as) = pitch a : toPitchesr as

toPitchesm :: [AbsPitch] -> [Pitch]
toPitchesm as = map pitch as

{-
Prove: toPitchesr as = toPitchesm as

Base Case: as = []
toPitchesr []
-> []
-> map pitch []
-> toPitchesm []

Induction Step: Assume toPitchesr as = toPitchesm as for all lists length n
Prove: toPitchesr (a:as) = toPitchesm (a:as)

toPitchesr (a:as)
-> pitch a : toPitchesr as
-> pitch a : toPitchesm as
-> pitch a : map pitch as
-> map pitch (a:as)
-> toPitchesm (a:as)
-}

chordr :: [Music a] -> Music a
chordr []     = rest 0
chordr (n:ns) = n :=: chordr ns

chordf :: [Music a] -> Music a
chordf ns = foldr (:=:) (rest 0) ns

{-
Prove: chordr ns = chordf ns for all finite ns

Base Case: Let ns = []
chordr []
-> rest 0
-> foldr (:=:) (rest 0) []
-> chordf []

Induction Step: Assume chordr ns = chordf ns for all ns of length n
Prove: chordr (n:ns) = chordf (n:ns)

chordr (n:ns)
-> n :=: chordr ns
-> n :=: chordf ns
-> n :=: (foldr (:=:) (rest 0) ns)
-> foldr (:=:) (rest 0) (n:ns)
-> chordf (n:ns)
-}

maxPitchr :: [Pitch] -> Pitch
maxPitchr [] = pitch 0
maxPitchr (p:ps) = p !!! maxPitchr ps

(!!!) :: Pitch -> Pitch -> Pitch
p1 !!! p2 = if absPitch p1 > absPitch p2 then p1 else p2

maxPitchf :: [Pitch] -> Pitch
maxPitchf ps = foldr (!!!) (pitch 0) ps

{-
Prove: maxPitchr ps = maxPitchf ps for all finite ps

Base Case: ps = []
maxPitchr []
-> pitch 0
-> foldr (!!!) (pitch 0) []
-> maxPitchf []

Induction Step: Assume maxPitchr ps = maxPitchf ps for ps of length n
Prove: maxPitchr (p:ps) = maxPitchf (p:ps)

maxPitchr (p:ps)
-> p !!! maxPitchr ps
-> p !!! maxPitchf ps
-> p !!! (foldr (!!!) (pitch 0) ps)
-> foldr (!!!) (pitch 0) (p:ps)
-> maxPitchf (p:ps)
-}

hNote :: Dur -> Pitch -> Music Pitch
hNote d p = note d p :=: note d (trans (-3) p)

hListr :: Dur -> [Pitch] -> Music Pitch
hListr d [] = rest 0
hListr d (p:ps) = hNote d p :+: hListr d ps

hListf :: Dur -> [Pitch] -> Music Pitch
hListf d ps = line $ map (hNote d) ps

{-
Prove: hListr d ps = hListf d ps for all finite ps

Base Case: ps = []
hListr d []
-> rest 0
-> line []
-> line $ map (hNote d) []
-> hListf d []

Induction Step: Assume hListr d ps = hListf d ps for all finte ps
Prove: hListr d (p:ps) = hListf d (p:ps)

hListr d (p:ps)
-> hNote d p :+: hListr d ps
-> hNote d p :+: hListf d ps
-> hNote d p :+: (line $ map (hNote d) ps)
-> line $ hNote d p : map (hNote d) ps
-> line $ map (hNote d) (p:ps)
-> hListf d (p:ps)
-}

{- 11.2: Prove as many of the properties in Figures 11.1 and 11.2 as you can.

MAP

Prove: map (\x -> x) as = (\x -> x) as
Proof by induction on as
Base Case: as = []
map (\x -> x) []
-> []
-> (\x -> x) [] 
Induction Step: 
Assume map (\x -> x) as = (\x -> x) as holds for arbitrary as of length n
Prove: map (\x -> x) (a:as) = (\x -> x) (a:as)
map (\x -> x) (a:as)
-> (\x -> x) a : map (\x -> x) as
-> (\x -> x) a : (\x -> x) as
-> (\x -> x) a : (\x -> x) as
-> (a:as)
-> (\x -> x) (a:as)

Prove: map (f . g) bs = (map f . map g) bs
Proof by induction on bs
Base Case: bs = []
map (f . g) []
-> []
-> map f []
-> map f (map g [])
-> (\xs -> map f (map g xs)) []
-> (map f . map g) []
Induction Step:
Assume map (f . g) bs = (map f . map g) bs for bs of arbitrary length n
Prove: map (f . g) (b:bs) = (map f . map g) (b:bs)
map (f . g) (b:bs)
-> (f . g) b : map (f . g) bs
-> (f . g) b : (map f . map g) bs
-> f(g(b)) : (map f . map g) bs
-> f(g(b)) : map f (map g bs)
-> map f ( g(b) : map g bs )
-> map f ( map g (b:bs) )
-> (map f . map g) (b:bs)

Prove: (map f . tail) cs = (tail . map f) cs
Proof by induction on cs
Base Case: cs = []
(map f . tail) []
-> map f (tail [])
-> map f ⊥
-> ⊥
-> tail []
-> tail (map f [])
-> (tail . map f) []
Induction Step: 
Assume (map f . tail) cs = (tail . map f) cs holds for arbitrary list cs length n
Prove (map f . tail) (c:cs) = (tail . map f) (c:cs)
(map f . tail) (c:cs)
-> map f (tail (c:cs))
-> map f cs
-> tail (map f (c:cs))
-> (tail . map f) (c:cs)
Did not use IH.

Prove: map f . reverse $ ds = reverse . map f $ ds
Proof by induction on ds.
Base Case: ds = []
map f . reverse $ []
-> map f (reverse [])
-> map f []
-> []
-> reverse []
-> reverse (map f [])
-> reverse . map f $ []
Induction Step: 
Assume map f . reverse $ ds = reverse . map f $ ds for arbitrary list length n
Prove: map f . reverse $ (d:ds) = reverse . map f $ (d:ds)
map f . reverse $ (d:ds)
-> map f (reverse (d:ds))
-> map f (reverse ds ++ [d]) *
-> map f (reverse ds) ++ map f [d]
-> map f (reverse ds) ++ [f d]
-> map f . reverse $ ds ++ [f d]
-> reverse . map f $ ds ++ [f d]
-> reverse (f d : reverse . map f $ ds)
-> reverse (map f (d:ds))
-> reverse . map f $ (d:ds)
* Lemma: see next proof

Prove: map f (xs ++ ys) = map f xs ++ map f ys
Induction on xs
Base Case: xs = []
map f ([] ++ ys)
-> map f ys
-> [] ++ map f ys
-> map f [] ++ map f ys
Induction Step: Assume map f (xs ++ ys) = map f xs ++ map f ys for arbitrary xs
Prove: map f ((x:xs) ++ ys) = map f (x:xs) ++ map f ys
map f ((x:xs) ++ ys)
-> map f (x : (xs ++ ys) )
-> f x : map f (xs ++ ys)
-> f x : map f xs ++ map f ys
-> map f (x:xs) ++ map f ys

Prove: map f . concat $ xs = concat . map (map f) $ xs
Proof by induction on is. Base Case: xs = []
map f . concat $ []
-> map f (foldr (++) [] [])
-> map f []
-> []
-> concat []
-> concat (map (map f) [])
-> concat . map (map f) $ []
Induction Step:
Assume map f . concat $ xs = concat . map (map f) $ xs
Prove map f . concat $ (x:xs) = concat . map (map f) $ (x:xs)
map f . concat $ (x:xs)
-> map f (concat (x:xs))
-> map f (foldr (++) [] (x:xs))
-> map f (x ++ foldr (++) [] xs)
-> map f (x ++ concat xs)
-> map f x ++ map f (concat xs)
-> map f x ++ map f . concat $ xs
-> map f x ++ concat . map (map f) $ xs
-> map f x ++ concat (map (map f) xs)
-> map f x ++ foldr (++) [] (map (map f) xs)
-> foldr (++) [] (map f x : map (map f) xs)
-> concat (map f x : map (map f) xs)
-> concat (map (map f) (x:xs))
-> concat . map (map f) $ (x:xs)

FOLD

Prove: 
If op is associative, i.e. (a `op` b) `op` c = a `op` (b `op` c)
and and e is an identity element, i.e. e `op` x = x and x `op` e = x for all x
then
foldr op e xs = foldl op e xs

Proof by Induction on xs
Base Case: xs = []
foldr op e []
-> e
-> foldl op e []

Induction Step: Assume foldr op e xs = foldl op e xs for xs of finite length
Prove foldr op e (x:xs) = foldl op e (x:xs)
foldl op e (x:xs)
-> foldl op (e `op` x) xs
-> foldl op x xs
-> x `op` foldl op e xs [Lemma below]
-> x `op` foldr op e xs
-> foldr op e (x:xs)

Lemma:
If op is associative and e is an identity element
foldl op y xs = y `op` foldl op e xs

Proof: Induction on xs
Base
foldl op y []
-> y
-> y `op` e
-> y `op` foldl op e []

Induction Step
foldl op y (x:xs)
-> foldl op (y `op` x) xs
-> (y `op` x) `op` foldl op e xs
-> y `op` (x `op` foldl op e xs)
-> y `op` ((e `op` x) `op` foldl op e xs)
-> y `op` foldl op (e `op` x) xs
-> y `op` foldl op e (x:xs)


Prove:
If   x `op1` (y `op2` z) = (x `op1` y) `op2` z
and  x `op1` e           =  e `op2` x

If  op1 x (op2 y z) = op2 (op1 x y) z
and op1 x e         = op2 e x

then for all finite xs
foldr op1 e xs = foldl op2 e xs

(Examples) 
op1 = flip (-), op2 = (-) , e = any integer
op1 = , op2 = , e =

In the  "middle" of the list, the foldr version "summarizes" the same interpretation 
the foldl version does just in a different order, starting from the last element 
in the list. How about e? Basically the second condition above says that the 
"ends" are same.

flip (-) x (y - z) = y - x - z
(y - z) - x = (y - x) - z

Proof: Induction on xs
Base Case
foldr op1 e []
-> e
-> foldl op2 e []

Induction Step
Assume foldr op1 e xs = foldl op2 e xs for xs of finite length
Prove foldr op1 e (x:xs) = foldl op2 e (x:xs)

foldl op2 e (x:xs)
-> foldl op2 (e `op2` x) xs
-> foldl op2 (x `op1` e) xs

{Lemma}
Prove: foldl op2 (y `op1` e) xs = y `op1` foldl op2 e xs
Proof by Induction: 
Base Case: foldl op2 (y `op1` e) []
-> y `op1` e
-> y `op1` foldl op2 e []
Induction Step:
Assume foldl op2 (y `op1` e) xs = y `op1` foldl op2 e xs for finite xs
Prove foldl op2 (y `op1` e) (x:xs) = y `op1` foldl op2 e (x:xs)
foldl op2 (y `op1` e) (x:xs)
-> foldl op2 ((y `op1` e) `op2` x) xs
-> foldl op2 (y `op1` (e `op2` x)) xs
-> y `op1` foldl op2 (e `op2` x) xs
-> y `op1` foldl op2 e (x:xs)
{End Lemma}

-> x `op1` foldl op2 e xs
-> x `op1` foldr op1 e xs
-> foldr op1 e (x:xs)

Prove:
For all finite xs
foldr op e xs = foldl (flip op) e (reverse xs)

Proof: Induction on xs
Base Case
foldr op e [] 
-> e 
-> foldl (flip op) e [] 
-> foldl (flip op) e (reverse [])

Induction Step
Assume foldr op e xs = foldl (flip op) e (reverse xs) for xs of finite length
Prove foldr op e (x:xs) = foldl (flip op) e (reverse (x:xs))
foldr op e (x:xs)
-> x `op` foldr op e (x:xs)
-> x `op` foldl (flip op) e (reverse xs)
-> foldl (flip op) e (reverse xs) `(flip op)` x

{Lemma}
foldl op e xs `op` y = foldl op e (xs ++ [y])
Proof: Induction on xs
Base Case
foldl op e [] `op` y
-> e `op` y
-> foldl op e [y]
-> foldl op e ([] ++ [y])
Induction Step
Assume foldl op e xs `op` y = foldl op e (xs ++ [y])
Prove foldl op e (x:xs) `op` y = foldl op e ((x:xs) ++ [y])
foldl op e (x:xs) `op` y 
-> foldl op (e `op` x) xs `op` y 
-> foldl op (e `op` x) (xs ++ [y])
-> foldl op e ((x:xs) ++ [y])
{End Lemma}

-> foldl (flip op) e (reverse xs ++ [x])
-> foldl (flip op) e (reverse (x:xs)

++

Prove
For all xs, ys and zs
(xs ++ ys) ++ zs = xs ++ (ys ++ zs)
Proof by Induction on xs:
Base Case
([] ++ ys) ++ zs
-> ys ++ zs
-> [] ++ (ys ++ zs)
Induction Step
Assume (xs ++ ys) ++ zs = xs ++ (ys ++ zs) for all lists xs of finite length
Prove ((x:xs) ++ ys) ++ zs = (x:xs) ++ (ys ++ zs)
((x:xs) ++ ys) ++ zs
-> (x : (xs ++ ys)) ++ zs
-> x : (xs ++ ys) ++ zs     [unfold ++]
-> x : xs ++ (ys ++ zs)     [IH]
-> (x:xs) ++ (ys ++ zs)     [fold ++]


Prove
For all xs
(xs ++ []) = ([] ++ xs) = xs
The second equality is true by definition.
So I'll prove the first equality using induction on xs
Base Case
[] ++ [] -> []

Induction Step
Assume (xs ++ []) = ([] ++ xs) = xs
Now to prove ((x:xs) ++ []) = ([] ++ (x:xs)) = (x:xs)
((x:xs) ++ [])
-> (x : xs ++ [])
-> (x : xs)
-> [] ++ (x:xs)     [fold ++]


TAKE AND DROP

For all finite non-negative m and n, and finite xs, prove the following...

Prove: take n xs ++ drop n xs = xs
Proof by Induction on n
Base Case
take 0 xs ++ drop 0 xs
-> [] ++ xs
-> xs
Induction Hypothesis
Assume take n xs ++ drop n xs = xs
Prove take (n+1) (x:xs) ++ drop (n+1) (x:xs) = (x:xs)
take (n+1) (x:xs) ++ drop (n+1) (x:xs)
-> x : take (n+1-1) xs ++ drop (n+1-1) xs
-> x : take n xs ++ drop n xs
-> (x:xs)


Prove: (take m . take n) xs = take (min m n) xs
Proof by Induction on n
Base Case
(take m . take 0) xs
-> take m (take 0 xs)
-> take m []
-> []
-> take 0 xs
-> take (min m 0) xs
Induction Step
Assume (take m . take n) xs = take (min m n) xs
Prove (take m . take (n+1)) xs = take (min m (n+1)) xs
Induction on xs
Base Case
(take m . take (n+1)) []
-> take m (take (n+1) [])
-> take m []
-> []
-> take (min m (n+1)) []
Assume (take m . take (n+1)) xs = take (min m (n+1)) xs
Prove (take m . take (n+1)) (x:xs) = take (min m (n+1)) (x:xs)
(take m . take (n+1)) (x:xs) 
-> take m (take (n+1) (x:xs))
-> take m (x : take n xs)
-> x : take (m-1) (take n xs)     [m /= 0]
-> x : take (min (m-1) n) xs
-> take (min (m-1) n + 1) (x:xs)
-> take (min m (n+1)) (x:xs)      [min m n + 1 = min (m+1) (n+1) (associativity +)]

Prove: drop m . drop n xs = drop (m+n) xs
Proof by Induction on n
Base Case
(drop m . drop 0) xs
-> drop m (drop 0 xs)
-> drop m xs
-> drop (m+0) xs
Induction Step
Assume drop m . drop n xs = drop (m+n) xs
Prove: drop m . drop (n+1) xs = drop (m+(n+1)) xs
Induction on xs
Base Case
drop m . drop (n+1) []
-> drop m (drop (n+1) [])
-> drop m []
-> []
-> drop (m+(n+1)) []
Induction Step
Assume drop m . drop (n+1) xs = drop (m + n + 1) xs
Prove drop m . drop (n+1) (x:xs) = drop (m + n + 1) (x:xs)
drop m . drop (n+1) (x:xs)
-> drop m (drop (n+1) (x:xs))
-> drop m (drop n xs)
-> drop (m+n) xs
-> drop ((m+n)+1) (x:xs)
-> drop (m+(n+1)) (x:xs)


Prove: take m . drop n xs = drop n . take (m + n) xs
Proof by Induction on n
Base Case:
(take m . drop 0) xs
-> take m (drop 0 xs)
-> take m xs
-> take (m+0) xs
-> drop 0 (take (m+0) xs)
-> (drop 0 . take (m+0)) xs
Induction Step
Assume take m . drop n xs = drop n . take (m + n) xs
Prove take m . drop (n+1) xs = drop (n+1) . take (m + (n+1)) xs
Induction on xs
Base Case
take m . drop (n+1) []
-> take m (drop (n+1) [])
-> take m []
-> []
-> drop (n+1) []
-> drop (n+1) (take (m+(n+1)) [])
-> (drop (n+1) . take (m+(n+1))) []
Induction Step
Assume take m . drop (n+1) xs = drop (n+1) . take (m + (n+1)) xs
Prove take m . drop (n+1) (x:xs) = drop (n+1) . take (m + (n+1)) (x:xs)
take m . drop (n+1) (x:xs)
-> take m (drop (n+1) (x:xs))
-> take m (drop n xs)
-> (take m . drop n) xs
-> (drop n . take (m+n)) xs
-> drop n (take (m+n) xs)
-> drop (n+1) (x : take (m+n) xs)
-> drop (n+1) (take ((m+n)+1) (x:xs))
-> drop (n+1) (take (m+(n+1)) (x:xs))
-> (drop (n+1) . take (m+(n+1))) (x:xs)


For all finite non-negative m and n such that n >= m
Prove (drop m . take n) xs = (take (n-m) . drop m) xs
Proof by Induction on n:
Base Case
drop m . take 0 xs
-> drop m (take 0 xs)
-> drop m []
-> []
-> take 0 (drop m xs)
-> (take (0-0) . drop m) xs
Induction Step
Assume (drop m . take n) xs = (take (n-m) . drop m) xs
Prove (drop m . take (n+1)) xs = (take ((n+1)-m) . drop m) xs
Induction on xs
Base Case
(drop m . take (n+1)) []
-> drop m (take (n+1) [])
-> drop m []
-> []
-> take ((n+1)-m) []
-> take ((n+1)-m) (drop m [])
-> (take ((n+1)-m) . drop m) xs
Induction Step
Assume (drop m . take (n+1)) xs = (take ((n+1)-m) . drop m) xs
Prove (drop m . take (n+1)) (x:xs) = (take ((n+1)-m) . drop m) (x:xs)
(drop m . take (n+1)) (x:xs)
-> drop m (take (n+1) (x:xs))
-> drop m (x : take n xs)
-> drop (m-1) (take n xs)
-> (drop (m-1) . (take n)) xs
-> (take (n-(m-1)) . drop (m-1)) xs
-> take (n-(m-1)) (drop (m-1) xs)
-> take (n-(m-1)) (drop m (x:xs))
-> take (n-m+1)) (drop m (x:xs))
-> take ((n+1)-m)) (drop m (x:xs))
-> (take ((n+1)-m) . drop m) (x:xs)


REVERSE
reverse = foldl (flip (:)) []


Prove: reverse (reverse xs) = xs
Proof
reverse (reverse xs)
-> foldl (flip (:)) [] (reverse xs)
-> foldr (:) [] xs
-> xs

Assume xs \= [] (otherwise head and last fail).
Prove: head (reverse xs) = last xs
Proof by Induction on xs
Base Case
head (reverse [x])
-> head [x]
-> x
-> last [x]
Induction Step
Assume head (reverse xs) = last xs is true for finite xs
Prove head (reverse (x:xs)) = last (x:xs)
head (reverse (x:xs))
-> head (reverse xs ++ [x])
{Lemma}
Prove head (zs ++ [y]) = head zs
Proof by Induction on zs
Base Case
head ([z] ++ [y])
-> head [z,y]
-> head z:[y]
-> z
-> head [z]
Induction Step:
Assume head (zs ++ ys) = head zs
Prove head ((z:zs) ++ ys) = head (z:zs)
head ((z:zs) ++ ys)
-> head (z : (zs ++ ys))
-> z
-> head (z:zs)
{End Lemma}
-> head (reverse xs)
-> last xs



Prove last (reverse xs) = head xs
Proof by Induction on xs
Base Case
last (reverse [x])
-> last [x]
-> x
-> head [x]
Induction Step
Assume last (reverse xs) = head xs
Prove last (reverse (x:xs)) = head (x:xs)
last (reverse (x:xs))
-> last (reverse xs ++ [x])
{Lemma}
Prove last (zs ++ [y]) =  y
Proof by Induction on zs
Base Case
last ([z] ++ [y])
-> last (z : [y])
-> last [y]
-> y
Induction Step
Assume last (zs ++ [y]) =  y
Prove last ((z:zs) ++ [y]) = y
Proof
last ((z:zs) ++ [y])
-> last ( z : (zs ++ [y]))
-> last (zs ++ [y])
-> y
{End Lemma}
-> x
-> head (x:xs)
-}




{- 11.3: Which of the following functions are strict (if the function takes more
 - than one argument, specify on which arguments it is strict):

reverse xs = foldl (flip (:)) []
STRICT

simple x y z = x * (y + z)
STRICT ON ALL ARGS

map f []     = []
map f (x:xs) = f x : map f xs
STRICT ON SECOND ARG because f is not "used" until we have (x:xs).
map _|_ does not equal _|_

tail (_:xs) = xs
STRICT

dur Prim(Note d _)       = d
dur Prim(Rest d)         = d
dur (m1 :+: m2)          = dur m1 + dur m2
dur (m1 :=: m2)          = max (dur m1) (dur m2)
dur (Modify (Tempo r) m) = dur m / r
dur (Modify _ m)         = dur m
STRICT

revM n@(Prim _) = n
revM (Modify c m) = Modify c (revM m)
revM (m1 :+: m2) = revM m2 :+: revM m1
revM (m1 :=: m2) = 
  let d1 = dur m1
      d2 = dur m2
  in if d1 > d2 then revM m1 :=: (rest (d1 - d2) :+: revM m2)
                else (rest (d2 - d1) :+: revM m1) :=: revM m2
STRICT

(&&)
True && x  = x
False && _ = False
STRICT ON FIRST ARG

(True &&) = \x -> x
STRICT

(False &&) = \_ -> False
NOT STRICT


ifFun :: Bool -> a -> a -> a
ifFun pred cons alt = if pred then cons 
                              else alt
STRICT ON FIRST ARG


{- 11.4: Recall Exercises 3.9 and 3.10. Prove that, if p2 >= p1
 -
 - chrom p1 p2 = mkScale p1 (take (absPitch p2 - absPitch p1)
 -                                (repeat 1))
 - using the lemma:
 -
 - [m..n] = scanl (+) m (take (n-m) (repeat 1))

Prove: 
If  p1 <= p2 and [m..n] = scanl (+) m (take (n-m) (repeat 1))
then 
chrom p1 p2 = mkScale p1 (take (absPitch p2 - absPitch p1) (repeat 1))
Proof:

chrom p1 p2
-> foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) [ap1..ap2]
-> foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) 
     $ scanl (+) ap1 (take (ap2-ap1) (repeat 1))
-> foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) 
     $ scanl (+) (absPitch p1) (take (absPitch p2 - absPitch p1) (repeat 1))


mkScale p1 (take (absPitch p2 - absPitch p1) (repeat 1))
-> foldr (\ap m -> note qn (pitch ap) :+: m) (rest 0) 
     $ scanl (+) (absPitch p1) (take (absPitch p2 - absPitch p1) (repeat 1))

 -}


{- Exercise 11.5: Prove the following facts involving dur:
 -
 - dur (timesM n m) = n * dur m
 - dur (cut d m)    = d, if d <= dur m

Prove: dur (timesM n m) = n * dur m
Proof by Induction on n
Base Case
dur (timesM 0 m)
-> dur (rest 0)
-> 0
-> 0 * dur m

Induction Step 
Assume dur (timesM n m) = n * dur m
Prove dur (timesM (n+1) m) = (n+1) * dur m
dur (timesM (n+1) m)
-> dur (m :+: timesM n m)
-> dur m + dur (timesM n m)
-> dur m + (n * dur m)
-> (n+1) * dur m




Prove: dur (cut d m) = d, if 0 <= d <= dur m
Proof by induction on m...

Base Cases

dur (cut d (Prim (Note oldD p)))
let d' = max (min oldD d) 0 = max d 0 = d
-> dur (if d'>0 then note d' p else rest 0)
-> dur (note d' p)
-> dur (Prim (Note d' p))
-> dur (Prim (Note d p))
-> d

dur (cut d (Prim (Rest oldD)))
-> dur (rest (max (min oldD d) 0))
-> dur (rest (max d 0))
-> dur (rest d)
-> dur (Prim (Rest d))
-> d

Induction Step:
dur (cut d (m1 :=: m2))
-> dur (cut d m1 :=: cut d m2)
-> dur (cut d m1) `max` dur (cut d m2)   [IH]
-> d `max` d
-> d

dur (cut d (m1 :+: m2))
let m'1 = cut d m1
    m'2 = cut (d - dur m'1) m2
-> dur (m'1 :+: m'2)
-> dur m'1 + dur m'2
-> d + (d - dur m'1)   [IH]
-> d + (d - d)
-> d

dur (cut d (Modify (Tempo r) m))
-> dur (tempo r (cut (d*r) m))
-> dur (Modify (Tempo r) (cut (d*r) m))
-> dur (cut (d*r) m) / r
-> d*r/r     [IH]
-> d
(Here we have to assume 0 <= d*r <= dur m)

dur (cut d (Modify c m))
-> dur (Modify c (cut d m))
-> dur (cut d m)
-> d             [IH]

-}



{- Exercise 11.6: Prove the following facts involving mMap:
 -
 - mMap id m         = m
 - mMap f (mMap g m) = mMap (f . g) m

Prove mMap id m = m
Proof by Induction on m

Base Cases...
m = Prim (Note d x)
mMap id (Prim (Note d x))
-> Prim (pMap id (Note d x))
-> Prim (Note d (id x))
-> Prim (Note d x)

m = Prim (Rest d)
mMap id (Prim (Rest d))
-> Prim (pMap id (Rest d))
-> Prim (Rest d)


Induction Step...
m = m1 :+: m2
mMap id (m1 :+: m2)
-> mMap id m1 :+: mMap id m2
-> m1 :+: m2

m = m1 :=: m2
mMap id (m1 :=: m2)
-> mMap id m1 :=: mMap id m2
-> m1 :=: m2

m = Modify c m1
mMap id (Modify c m1)
-> Modify c (mMap id m1)
-> Modify c m1



Prove mMap f (mMap g m) = mMap (f . g) m
Proof by Induction on m
Base case

m = Prim (Note d x)
mMap f (mMap g (Prim (Note d x)))
-> mMap f (Prim (pMap g (Note d x)))
-> mMap f (Prim (Note d (g x)))
-> Prim (pMap f (Note d (g x)))
-> Prim (Note d (f(g(x))))
-> Prim (Note d ((f . g) x))
-> Prim (pMap (f . g) (Note d x))
-> mMap (f . g) (Prim (Note d x))

m = Prim (Rest d)
mMap f (mMap g (Prim (Rest d)))
-> mMap f (Prim (pMap g (Rest d)))
-> mMap f (Prim (Rest d))
-> Prim (pMap f (Rest d))
-> Prim (Rest d)
-> Prim (pMap (f . g) (Rest d))
-> mMap (f . g) (Prim (Rest d))


Induction Step
m = m1 :+: m2
mMap f (mMap g (m1 :+: m2))
-> mMap f (mMap g m1 :+: mMap g m2)
-> mMap f (mMap g m1) :+: mMap f (mMap g m2)
-> mMap (f . g) m1 :+: mMap (f . g) m2
-> mMap (f . g) (m1 :+: m2)

m = m1 :=: m2
mMap f (mMap g (m1 :=: m2))
-> mMap f (mMap g m1 :=: mMap g m2)
-> mMap f (mMap g m1) :=: mMap f (mMap g m2)
-> mMap (f . g) m1 :=: mMap (f . g) m2
-> mMap (f . g) (m1 :=: m2)

m = Modify c m1
mMap f (mMap g (Modify c m1))
-> mMap f (Modify c (mMap g m1))
-> Modify c (mMap f (mMap g m1))
-> Modify c (mMap (f . g) m1)
-> mMap (f . g) (Modify c m1)

-}




{- Exercise 11.7: 
 - Prove for all pmap, c, and m
 -
 - perf pmap c m = (perform pmap c m, dur m * cDur c)  [Corrected]

perform :: PMap a -> Context a -> Music a -> Performance
perform pm
  c@Context {cTime = t,cPlayer = pl,cDur = dt,cKey = k} m =
  case m of
    Prim (Note d p)         -> playNote pl $ c d p
    Prim (Rest d p)         -> []
    m1 :+: m2               ->
      let c' = c{cTime = t + dur m1 * dt}
      in perform pm c m1 ++ perform c' m2
    m1 :=: m2               -> merge (perform pm c m1)
                       (perform pm c m2)
    Modify (Tempo r) m      -> perform pm (c{cDur = dt/r}) m
    Modify (Transpose p) m  -> perform pm (c{Key = k + p}) m
    Modify (Instrument i) m -> perform pm (c{cInst = i}) m
    Modify (Player pn) m    -> perform pm (c{cPlayer = pm pn}) m
    Modify (Phrase pas) m   -> interpPhrase pl pm c pas m


perf :: PMap a -> Context a -> Music a -> (Performance, DurT)
perf pm
  c@Context{cTime = t,cPlayer = pl, cDur = dt,cKey = k} m =
  case m of
    Prim (Note d p)         -> (playNote pl $ c d p, d*dt)
    Prim (Rest d)           -> ([],d*dt)
    m1 :+: m2               ->
      let (pf1,d1) = perf pm c m1
          (pf2,d2) = perf pm (c{cTime = t + d1}) m2
      in (pf1 ++ pf2, d1+d2)
    m1 :=: m2               ->
      let (pf1,d1) = perf pm c m1
          (pf2,d2) = perf pm (c{cTime = t + d1}) m2
      in (merge pf1 pf2,max d1 d2)
    Modify (Tempo r) m      -> perform pm (c{cDur = dt/r}) m
    Modify (Transpose p) m  -> perform pm (c{Key = k + p}) m
    Modify (Instrument i) m -> perform pm (c{cInst = i}) m
    Modify (Player pn) m    -> perform pm (c{cPlayer = pm pn}) m
    Modify (Phrase pas) m   -> interpPhrase pl pm c pas m

Proof by induction on m:
Base Case
m = Prim (Note d p)
perf pmap c{cPlayer=pl,cDur=dt} (Prim (Note d p))
-> (playNote pl $ c d p,d*dt)
-> (perform pmap c{cPlayer=pl,cDur=dt} (Prim (Note d p)),d*dt)
-> (perform pmap c{cPlayer=pl,cDur=dt} (Prim (Note d p)),dur m * cDur c)

m = Prim (Rest d)
perf pmap c{cPlayer=pl,cDur=dt} (Prim (Rest d))
-> ([],d*dt)
-> (perform pmap c{cPlayer=pl,cDur=dt} (Prim (Rest d)),d*dt)
-> (perform pmap c{cPlayer=pl,cDur=dt} (Prim (Rest d)),dur m * cDur c)


Induction Step

m  = m1 :+: m2
t  = cTime c
dt = cDur c

perf pmap c (m1 :+: m2)
-> let (pf1,d1) = perf pm c m1
       (pf2,d2) = perf pm (c{cTime = t + d1}) m2
   in (pf1 ++ pf2, d1+d2)
-> (perform pmap c m1 ++ perform pmap (c{cTime = t + dur m1 * dt}) m2
   ,dur m1 * dt + dur m2 * dt) [IH]
-> (perform pmap c m1 ++ perform pmap (c{cTime = t + dur m1 * dt}) m2
   , (d1 + d2) * dt)
-> (perform pmap c m1 ++ perform pmap (c{cTime = t + dur m1 * dt}) m2
   , dur (m1 + m2) * dt)
-> (perform pmap c (m1 :+: m2) , dur (m1 :+: m2) * cDur c)


m = m1 :=: m2
perf pmap c (m1 :=: m2)
-> let (pf1,d1) = perf pm c m1
       (pf2,d2) = perf pm c m2
   in (merge pf1 pf2, max d1 d2)
-> (merge (perform pm c m1) (perform pm c m2), max (dur m1 * cDur c) (dur m2 * cDur c))
-> (perform pm c (m1 :=: m2), dur (m1 :=: m2) * cDur c) 


m = Modify (Tempo r) m1
dt = cDur c
perf pmap c (Modify (Tempo r) m1)
-> perf pm (c{cDur = dt/r}) m1
-> (perform pm (c{cDur = dt/r}) m1, dur m1 * (dt/r))
-> (perform pm (c{cDur = dt/r}) m1, (dur m1 / r) * dt)
-> (perform pm c (Modify (Tempo r) m), dur (Modify (Tempo r) m) * dt) 
-> (perform pm c (Modify (Tempo r) m), dur (Modify (Tempo r) m) * cDur c) 


- perf pmap c m = (perform pmap c m, dur m * cDur c)  [Corrected]

m = Modify (Transpose p) m1
perf pmap c (Modify (Transpose p) m1)
-> perf pm (c{cKey=k+p}) m1
-> (perform pmap (c{cKey=k+p}) m1, dur m1 * cDur (c{cKey=k+p}))
-> (perform pmap c (Modify (Transpose p) m1), dur m1 * cDur c)
-> (perform pmap c (Modify (Transpose p) m1), dur (Modify (Transpose p) m1) * cDur c)


m = Modify (Instrument i) m1
perf pmap c (Modify (Instrument i) m1)
-> perf pm (c{cInst=i}) m1
-> (perform pmap (c{cInst=i}) m1, dur m1 * cDur (c{cInst=i}))
-> (perform pmap c (Modify (Instrument i) m1), dur m1 * cDur c)
-> (perform pmap c (Modify (Instrument i) m1), dur (Modify (Instrument i) m1) * cDur c)


m = Modify (Player pn) m1
perf pmap c (Modify (Player pn) m1)
-> perf pm (c{cPlayer=pmap pn}) m1
-> (perform pmap (c{cPlayer=pmap pn}) m1, dur m1 * cDur (c{cPlayer=pmap pn}))
-> (perform pmap c (Modify (Player pn) m1), dur m1 * cDur c)
-> (perform pmap c (Modify (Player pn) m1), dur (Modify (Player pn) m1) * cDur c)

(Here we assume a player that takes a "musically sound" approach)
m = Modify (Phrase pas) m1
c1 = Context c{cPlayer=pl} 
perf pmap c1 (Modify (Phrase pas) m1)
-> interpPhrase pl pmap c1 pas m1
-> let (pf,dur) = perf pmap c1 m1
   in (foldr pasHandler (perform pmap c1 m1) pas, dur m1 * cDur c1)
-> (interpPhrase pl pmap c1 pas m1, dur m1 * cDur c1)
-> (perform pmap c1 (Modify (Phrase pas) m1), dur m1 * cDur c1)


























