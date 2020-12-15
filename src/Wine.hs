module Wine (
  Wine(..),
  Origin(..),
  completeOrigin,
  vintageRating,
  Rating
) where

import Prelude hiding (lookup)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)

type Vintage = Int
type Rating = Int

data Wine = Wine 
  { origin :: Origin
  , year  :: Vintage
  }

completeOrigin :: Origin -> [Origin]
completeOrigin o = case o of
                     Bordeaux -> [Bordeaux]
                     _ -> o : completeOrigin (getEnclosingRegion o)

data Origin = Bordeaux | BordeauxSuperieur |
  NorthLeftBank | SouthLeftBank | RightBank | EntreDeuxMersBank |
  Medoc | HautMedoc | StEstephe | Pauillac | StJulien |
  ListracMedoc | MoulisEnMedoc | Moulis | Margaux | SaintEstephe |
  SaintJulien |
  PessacLeognan | Graves | Cerons | Barsac | Sauternes |
  GravesSuperieures |
  CotesDeBourg | CotesDeBlaye | PremieresCotesDeBlaye |
  Fronsac | CannonFronsac | Pomerol | LalandeDePomerol | SaintEmilion |
  SaintEmilionGrandCru | MontagneSaintEmilion | SaintGeorgesSaintEmilion | 
  LussacSaintEmilion | PuisseguinSaintEmilion | CotesDeCastillon |
  BordeauxCotesDeFrancs | CotesDeFrancs | StEmilion |
  EntreDeuxMers | GravesDeVayres | Cadillac | Loupiac |
  SainteCroixDuMont | BordeauxHautBenauge | EntreDeuxMersHautBenauge |
  CotesDeBordeauxSaintMacaire | SainteFoyBordeaux
  deriving (Eq,Read,Show)


vintageRating :: Wine -> Maybe Rating
vintageRating wine = 
  case origin wine of 
    Pomerol -> Map.lookup (year wine) pomerol
    StEmilion -> Map.lookup (year wine) stEmilion
    SaintEmilion -> Map.lookup (year wine) stEmilion
    Pauillac -> Map.lookup (year wine) julienPauillacEstephe
    SaintJulien -> Map.lookup (year wine) julienPauillacEstephe
    StJulien -> Map.lookup (year wine) julienPauillacEstephe
    StEstephe -> Map.lookup (year wine) julienPauillacEstephe
    SaintEstephe -> Map.lookup (year wine) julienPauillacEstephe
    Margaux -> Map.lookup (year wine) margaux
    Bordeaux ->
      estimateVintage (year wine) [julienPauillacEstephe,stEmilion,gravesPessac]
    _ ->
      case getEnclosingRegion $ origin wine of
        NorthLeftBank -> 
          estimateVintage (year wine) [julienPauillacEstephe, margaux]
        SouthLeftBank -> 
          Map.lookup (year wine) gravesPessac
        RightBank ->
          estimateVintage (year wine) [stEmilion, pomerol]
        EntreDeuxMersBank->
          estimateVintage (year wine) [stEmilion, gravesPessac]
        Bordeaux ->
          estimateVintage (year wine) [julienPauillacEstephe,stEmilion,gravesPessac]
        _ -> 
          estimateVintage (year wine) [julienPauillacEstephe,stEmilion,gravesPessac]
                       
getEnclosingRegion :: Origin -> Origin
getEnclosingRegion r 
  = case r of 
      NorthLeftBank -> Bordeaux; SouthLeftBank -> Bordeaux; 
      RightBank -> Bordeaux; EntreDeuxMersBank -> Bordeaux;
      BordeauxSuperieur -> Bordeaux;

      Medoc -> NorthLeftBank; HautMedoc -> NorthLeftBank;
      StEstephe -> NorthLeftBank; Pauillac -> NorthLeftBank;
      StJulien -> NorthLeftBank; ListracMedoc -> NorthLeftBank;
      MoulisEnMedoc -> NorthLeftBank; Moulis -> NorthLeftBank;  
      Margaux -> NorthLeftBank; SaintEstephe -> NorthLeftBank;
      SaintJulien -> NorthLeftBank;

      PessacLeognan -> SouthLeftBank; Graves -> SouthLeftBank;
      Cerons -> SouthLeftBank; Barsac -> SouthLeftBank; 
      Sauternes -> SouthLeftBank; GravesSuperieures -> SouthLeftBank;

      CotesDeBourg -> RightBank; CotesDeBlaye -> RightBank; 
      PremieresCotesDeBlaye -> RightBank; Fronsac -> RightBank;
      CannonFronsac -> RightBank; Pomerol -> RightBank; 
      LalandeDePomerol -> RightBank; SaintEmilion -> RightBank; 
      SaintEmilionGrandCru -> RightBank; MontagneSaintEmilion -> RightBank; 
      SaintGeorgesSaintEmilion -> RightBank; LussacSaintEmilion -> RightBank; 
      PuisseguinSaintEmilion -> RightBank; CotesDeCastillon -> RightBank; 
      BordeauxCotesDeFrancs -> RightBank; CotesDeFrancs -> RightBank;  
      StEmilion -> RightBank; 

      EntreDeuxMers -> EntreDeuxMersBank; GravesDeVayres -> EntreDeuxMersBank; 
      Cadillac -> EntreDeuxMersBank; Loupiac -> EntreDeuxMersBank; 
      SainteCroixDuMont -> EntreDeuxMersBank; 
      BordeauxHautBenauge -> EntreDeuxMersBank; 
      EntreDeuxMersHautBenauge -> EntreDeuxMersBank; 
      CotesDeBordeauxSaintMacaire -> EntreDeuxMersBank;  
      SainteFoyBordeaux -> EntreDeuxMersBank; 


type VintageChart = Map.Map Vintage Rating

bordeauxVintages = 1970 : 1971 : 1975 : 1976 : 1978 : [1979 .. 2016]

julienPauillacEstephe :: VintageChart
julienPauillacEstephe = 
  Map.fromList $ zip
  bordeauxVintages
  ([87,82,89,84,87,85,78,85,98,86,72,90,94,82,87,90,98,75,79,78,85,92,96] ++
   [84,87,88,96,88,88,95,88,95,87,86,91,99,98,88,92,81,93,95,98])

margaux :: VintageChart
margaux =
  Map.fromList $ zip
  bordeauxVintages
  ([85,83,78,77,87,87,79,82,86,95,68,86,90,76,85,86,90,74,75,77,85,88,88] ++
   [82,86,89,94,89,88,88,87,98,88,86,90,97,95,87,89,80,90,96,97]) 

gravesPessac :: VintageChart
gravesPessac =
  Map.fromList $ zip
  bordeauxVintages
  ([87,86,89,71,88,88,78,84,88,89,79,90,89,84,89,89,90,74,75,86,88,89,86] ++
   [86,94,88,97,88,87,88,88,96,87,87,91,98,99,86,91,81,93,96,97])

pomerol :: VintageChart
pomerol =
  Map.fromList $ zip
  bordeauxVintages
  ([90,87,94,82,84,86,79,86,96,90,65,88,87,85,89,96,96,58,82,87,89,92,85] ++
   [87,96,88,95,90,85,84,88,95,90,86,96,98,95,88,94,84,94,96,97]) 

stEmilion :: VintageChart
stEmilion =
  Map.fromList $ zip
  bordeauxVintages
  ([85,83,85,82,84,84,72,82,94,89,69,87,88,74,88,88,98,59,75,84,86,88,87] ++ 
   [86,96,88,96,90,87,90,88,99,88,86,92,93,94,87,93,82,92,95,95])

estimateVintage :: Vintage -> [VintageChart] -> Maybe Rating
estimateVintage v proxies = let ratings = catMaybes $ map (Map.lookup v) proxies
                            in Just $ sum ratings `quot` length ratings
