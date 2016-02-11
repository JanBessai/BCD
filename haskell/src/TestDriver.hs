{-# LANGUAGE TemplateHaskell
             , DeriveDataTypeable
             , StandaloneDeriving
             , DeriveGeneric #-}


import GHC.Generics (Generic)
import Control.Applicative
import Control.DeepSeq
import Control.Exception (evaluate)
import Criterion.Main
import Data.Typeable
import Test.QuickCheck
import Data.Time.Exts.Unix
import qualified BCD as BCD

instance Show BCD.IntersectionType where
  showsPrec _ BCD.Omega = showString "ω"
  showsPrec _ (BCD.Var x) =
    let index = 1 + (x `div` 6) in
    showString $ 
      (['α', 'β', 'γ', 'δ', 'ε', 'ζ'] !! (x `mod` 6)) :
      (if index > 1 then show index else "")
  showsPrec d (BCD.Arr src tgt) =
    showParen (d > arr_prec) $ 
      showsPrec (arr_prec + 1) src 
      . showString " → " 
      . showsPrec (arr_prec + 1) tgt
    where arr_prec = 5
  showsPrec d (BCD.Inter l r) =
    showParen (d > inter_prec) $ 
      showsPrec (inter_prec + 1) l
      . showString " ∩ " 
      . showsPrec (inter_prec + 1) r
    where inter_prec = 6

genType :: Int -> Gen BCD.IntersectionType
genType n | n > 3 = do
  nLeft <- abs <$> resize (n - 1) arbitrarySizedIntegral  
  oneof [ BCD.Arr <$> (genType nLeft) <*> (genType (n - 1 - nLeft))
        , BCD.Inter <$> (genType nLeft) <*> (genType (n - 1 - nLeft))
        ]
genType _ = 
  oneof [ pure BCD.Omega
        , BCD.Var . abs <$> arbitrarySizedIntegral
        ]

benchData :: Int -> Int -> Int -> Gen [(Int, [BCD.IntersectionType])]
benchData perSize step max =
  mapM (\ n -> (,) n <$> vectorOf perSize (genType n)) $ 1 : tail [0, step .. max]


worstCase :: Int -> (BCD.IntersectionType, BCD.IntersectionType)
worstCase n =
  (worstCaseLeft n, worstCaseRight n)
  where
    worstCaseLeft n =
      foldl (\ s n' -> 
        BCD.Inter s $ BCD.Arr
          (BCD.Var n')
          (BCD.Var n')) BCD.Omega [1 .. n]
    worstCaseRight n =
      foldl (\ s n' ->
        let tau = foldl (\ s' m ->
                      if n' == m then s' 
                      else (BCD.Inter s' (BCD.Var m)))
                    BCD.Omega [1..n]
        in BCD.Inter s $ BCD.Arr tau tau) BCD.Omega [1..n]
          

instance Generic BCD.IntersectionType
instance NFData BCD.IntersectionType where rnf x = seq x ()

deriving instance Show BCD.Sumbool
instance Generic BCD.Sumbool
instance NFData BCD.Sumbool where rnf x = seq x ()


setupEnv :: IO [(Int, [(BCD.IntersectionType, BCD.IntersectionType) ])]
setupEnv = do
  tysLeft <- generate $ benchData 1 10 200
  tysRight <- generate $ benchData 1 10 200
  return $ zipWith toPairs tysLeft tysRight
  where
    toPairs (n, tysl) (_, tysr) =
      (n, zip tysl tysr)


setupWorstCaseEnv :: IO [(Int, (BCD.IntersectionType, BCD.IntersectionType))]
setupWorstCaseEnv = do
  return $ map (\ n ->
    let tys@(l, r) = worstCase n in
    (max (measure l) (measure r), tys)) [0, 10 .. 200]


measure BCD.Omega = 1
measure (BCD.Var _) = 1
measure (BCD.Arr l r) = 1 + measure l + measure r
measure (BCD.Inter l r) = 1 + measure l + measure r

 
timeIt :: (NFData a, NFData b) => (a -> b) -> a -> IO (Double, b)
timeIt action arg = do
  arg' <- evaluate $ force arg
  print "starting..."
  startTime <- _udt_mic_base <$> getCurrentUnixDateTimeMicros
  -- startTime <- getCPUTime
  r <- evaluate $ force $ action arg'
  -- finishTime <- getCPUTime
  finishTime <- _udt_mic_base <$> getCurrentUnixDateTimeMicros
  return (fromIntegral (finishTime - startTime) / 100, r)

main :: IO ()
main = do
  let tys = replicate 100 (worstCase 200)
  {-(t, r) <- timeIt (map (uncurry BCD.subtype_decidable)) tys
  print t
  print (head r)
  print . (\ (l, r) -> max (measure l) (measure r) ) . head $ tys -}
  defaultMain 
    [ env setupWorstCaseEnv $ \ tys ->
        bgroup "worst case subtyping" $
          (bench "dummy" $ whnf (+ 1) 1) :
            map (\ (n, tysn) -> bench ("type_size_" ++ show n) $ nf subtypes tysn) tys
    {-env setupEnv $ \ ~tys ->
      bgroup "subtyping" $
        (bench "dummy" $ whnf (+ 1) 1) :  
        map (\ (n, tysn) -> bench ("type_size_" ++ show n) $ nf (map subtypes) tysn) tys -}
    ]
  where
    subtypes = uncurry $ BCD.subtype_decidable
  
