data Type = TInt
          | TTop
          | TArrow Type Type
          | TAnd Type Type
          deriving (Eq, Show)


-- ordinary type

ordinaryD :: Type -> Bool
ordinaryD a = splitD a == Nothing



-- split type

splitD :: Type -> Maybe (Type, Type)

splitD (TAnd a b) = Just (a, b)
splitD (TArrow a b)
  | Just (b1, b2) <- splitD b
  = Just (TArrow a b1, TArrow a b2)
splitD _ = Nothing
  



-- subtyping

checkSub :: Type -> Type -> Bool
checkSub TInt TInt = True                                 -- IS-int
checkSub _ TTop    = True                                 -- IS-top
checkSub a b                                              -- IS-and
  | Just (b1, b2) <- splitD b
  = checkSub a b1 && checkSub a b2
checkSub (TAnd a1 a2) b                                   -- IS-andl IS-andr
  = checkSub a1 b || checkSub a2 b
checkSub (TArrow a1 a2) (TArrow b1 b2)                    -- IS-arrow
  = checkSub b1 a1 && checkSub a2 b2
checkSub _ _ = False



-- Pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"


showtest :: Type -> Type -> String
showtest a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (checkSub a b)
  


-- examples
t0 = TArrow TInt TInt
t1 = (TArrow (TInt) (TAnd TInt TInt))
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)

test1 = showtest t1 t1                                                              -- True

test5 = showtest (TArrow TInt TTop) t0                                              -- False
test6 = showtest t0 (TArrow TInt TTop)                                              -- True

test10 = showtest (TAnd t0 TInt) (TAnd t0 TInt)                                     -- True

test12 = showtest (TAnd t0 TInt) t0                                                 -- True
test13 = showtest t0 (TAnd t0 TInt)                                                 -- False
