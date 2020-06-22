import HSfst

-- Example Grammars:
-- Majority rules don't work in HS!
testMajority :: [String]
testMajority = map (converge majorityRules) ["aa","aab","aabb","aabbb"]
majorityRules :: (CON Char,GEN Char)
majorityRules = (con,gen) 
       where
              gen = mkGen "ab"
              con = [dep,ident',noAB,noBA,max']
              dep = mkDep "ab" (const True)
              ident' = mkId "ab" (==)
              noAB = mkMark "ab" (mkPreds $ SQ False "ab" False)
              noBA = mkMark "ab" (mkPreds $ SQ False "ba" False)
              max' = mkMax "ab" (const True)

-- cvcvc wins rather than cvccvc, why is that candidate not mentioned in the paper?
testArabic :: String
testArabic = converge classicalArabic "ccvc" -- ccvc ~ f?al; cvcvc ~ fi?al wins!; cvccvc ~ ?if?al does not win?!
classicalArabic :: (CON Char,GEN Char)
classicalArabic = (con,gen)
       where
              gen = mkGen "cv"
              con = [noCO,max',ident',onset,dep]
              noCO = mkMark "cv" (mkPreds $ SQ True "cc" False)
              max' = mkMax "cv" (const True)
              ident' = mkId "cv" (==)
              onset = mkMark "cv" (mkPreds $ SQ True "v" False)
              dep = mkDep "cv" (const True)

-- Just a fun one for testing, since it contains many different types of constraints.
testSino :: [String]
testSino = converge' sinoToAnton "sino"
sinoToAnton :: (CON Char,GEN Char)
sinoToAnton = (con,gen)
       where
              gen = mkGen "antosi"
              con = [ident',maxO,maxN,noS,noI,no_N,noNO,noNAO,noO_,depO,depT,depA,max',dep']
              ident' = mkId "antosi" (==)
              maxO = mkMax "antosi" (=='o')
              maxN = mkMax "antosi" (=='n')
              noS = mkMark "antosi" (mkPreds $ SQ False "s" False)
              noI  = mkMark "antosi" (mkPreds $ SQ False "i" False)
              no_N = mkMark "antosi" (mkPreds $ SQ True "n" False)
              noNO = mkMark "antosi" (mkPreds $ SQ False "no" False)
              noNAO = mkMark "antosi" (mkPreds $ SQ False "nao" False)
              noO_ = mkMark "antosi" (mkPreds $ SQ False "o" True)
              depO = mkDep "antosi" (=='o')
              depT = mkDep "antosi" (=='t')
              depA = mkDep "antosi" (=='a')
              max' = mkMax "antosi" (const True)
              dep' = mkDep "antosi" (const True) 