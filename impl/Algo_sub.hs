data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TAnd Type Type
          | TOr Type Type
          deriving (Eq, Show)


-- ordinary type

ordinaryD :: Type -> Bool
ordinaryD a = splitD a == Nothing

ordinaryC :: Type -> Bool
ordinaryC a = splitC a == Nothing


-- split type

splitD :: Type -> Maybe (Type, Type)

splitD (TAnd a b) = Just (a, b)
splitD (TArrow a b)
  | Just (b1, b2) <- splitD b
  = Just (TArrow a b1, TArrow a b2)
splitD (TArrow a b)
  | Just (a1, a2) <- splitC a
  = Just (TArrow a1 b, TArrow a2 b)
splitD (TOr a b)
  | Just (a1, a2) <- splitD a
  = Just (TOr a1 b, TOr a2 b)
splitD (TOr a b)
  | Just (b1, b2) <- splitD b
  = Just (TOr a b1, TOr a b2)
splitD _ = Nothing
    
splitC (TOr a b) = Just (a, b)
splitC (TAnd a b)
  | Just (a1, a2) <- splitC a
  = Just (TAnd a1 b, TAnd a2 b)
splitC (TAnd a b)
  | Just (b1, b2) <- splitC b
  = Just (TOr a b1, TOr a b2)
splitC _ = Nothing
  



-- subtyping

checkSub :: Type -> Type -> Bool
checkSub TInt TInt = True                                                          -- S-int
checkSub _ TTop    = True                                                          -- S-top
checkSub TBot _    = True                                                          -- S-bot
checkSub a b                                                                       -- S-and
  | Just (b1, b2) <- splitD b
  = checkSub a b1 && checkSub a b2
checkSub a b                                                                       -- S-andl S-andr
  | Just (a1, a2) <- splitD a
  = checkSub a1 b || checkSub a2 b
checkSub a b                                                                       -- S-or
  | Just (a1, a2) <- splitC a
  = checkSub a1 b && checkSub a2 b
checkSub a b                                                                       -- S-orl S-orr
  | Just (b1, b2) <- splitC b
  = checkSub a b1 || checkSub a b2
checkSub (TArrow a1 a2) (TArrow b1 b2)                                             -- S-arr
  = checkSub b1 a1 && checkSub a2 b2
checkSub _ _ = False



-- Pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOr a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Type -> Type -> String
showtest a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (checkSub a b)
  


-- examples
t0 = TArrow TInt TInt
t1 = (TArrow (TInt) (TAnd TInt TInt))
t2 = TArrow (TOr TInt t0) TInt
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)

test1 = showtest t1 t1                                                              -- True

test3 = showtest t2 t3                                                              -- True
test4 = showtest TBot TInt                                                          -- True
test5 = showtest (TArrow TInt TTop) t0                                              -- False
test6 = showtest t0 (TArrow TInt TTop)                                              -- True

test10 = showtest (TAnd t0 TInt) (TAnd t0 TInt)                                     -- True
test11 = showtest (TOr t0 TInt) (TOr t0 TInt)                                       -- True

test12 = showtest (TAnd t0 TInt) t0                                                 -- True
test13 = showtest t0 (TAnd t0 TInt)                                                 -- False
test14 = showtest (TOr t0 TInt) t0                                                  -- False
test15 = showtest t0 (TOr t0 TInt)                                                  -- True
