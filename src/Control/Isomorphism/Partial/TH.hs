{-# LANGUAGE TemplateHaskell #-}
module Control.Isomorphism.Partial.TH 
  ( constructorIso
  , defineIsomorphisms
  ) where

import Language.Haskell.TH
import Control.Monad
import Data.List (find)
import Data.Char (toLower)

import Control.Isomorphism.Partial.Unsafe (Iso (Iso))

-- | Extract the name of a constructor, e.g. ":" or "Just".
conName :: Con -> Name
conName (NormalC name fields)       =   name
conName (RecC name fields)          =   name
conName (InfixC lhs name rhs)       =   name
conName (ForallC vars context con)  =   conName con

-- | Extract the types of the constructor's fields.
conFields :: Con -> [Type]
conFields (NormalC name fields)       =   map (\(s, t) -> t) fields
conFields (RecC name fields)          =   map (\(n, s, t) -> t) fields
conFields (InfixC lhs name rhs)       =   map (\(s, t) -> t) [lhs, rhs]
conFields (ForallC vars context con)  =   conFields con

-- | Extract the constructors of a type declaration
decConstructors :: Dec -> Q [Con]
decConstructors (DataD _ _ _ cs _)    =  return cs
decConstructors (NewtypeD _ _ _ c _)  =  return [c]
decConstructors _                      
  = fail "partial isomorphisms can only be derived for constructors of data type or newtype declarations."

-- | Construct a partial isomorphism expression for a constructor, 
-- given the constructor's name.
constructorIso :: Name -> ExpQ
constructorIso c = do
  DataConI n _ d _  <-  reify c
  TyConI dec        <-  reify d
  cs                <-  decConstructors dec
  let Just con      =   find (\c -> n == conName c) cs
  isoFromCon (wildcard cs) con

wildcard :: [Con] -> [MatchQ]
wildcard cs 
  =  if length cs > 1
     then  [match (wildP) (normalB [| Nothing |]) []]
     else  []

-- | Converts a constructor name (starting with an upper-case
--   letter) into a function name (starting with a lower-case
--   letter).
rename :: Name -> Name
rename n 
  = mkName (toLower c : cs) where c : cs = nameBase n

-- | Construct partial isomorphism definitions for all 
--   constructors of a datatype, given the datatype's name.
--   The names of the partial isomorphisms are constructed by
--   spelling the constructor names with an initial lower-case
--   letter.
defineIsomorphisms :: Name -> Q [Dec]
defineIsomorphisms d = do
  TyConI dec  <-  reify d
  cs          <-  decConstructors dec
  mapM (defFromCon (wildcard cs)) cs

-- | Constructs a partial isomorphism definition for a
--   constructor, given information about the constructor.
--   The name of the partial isomorphisms is constructed by
--   spelling the constructor name with an initial lower-case
--   letter.
defFromCon :: [MatchQ] -> Con -> DecQ
defFromCon wildcard con
  = funD (rename (conName con)) 
      [clause [] (normalB (isoFromCon wildcard con)) []]

-- | Constructs a partial isomorphism expression for a
--   constructor, given information about the constructor.
isoFromCon :: [MatchQ] -> Con -> ExpQ
isoFromCon wildcard con = do
  let c     =   conName con
  let fs    =   conFields con
  let n     =   length fs
  (ps, vs)  <-  genPE n
  v         <-  newName "x"
  let f     =   lamE [nested tupP ps] 
                  [| Just $(foldl appE (conE c) vs) |]
  let g     =   lamE [varP v] 
                  (caseE (varE v) $ 
                    [ match (conP c ps) 
                        (normalB [| Just $(nested tupE vs) |]) []
                    ] ++ wildcard)
  [| Iso $f $g |]



genPE n = do
  ids <- replicateM n (newName "x")
  return (map varP ids, map varE ids)

nested tup []      =  tup [] 
nested tup [x]     =  x
nested tup (x:xs)  =  tup [x, nested tup xs]
