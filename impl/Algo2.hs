data Mode = MSub | MSuper
          deriving (Eq, Show)
          
data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TOp Mode Type Type -- MSub for and, MSuper for or
          deriving (Eq, Show)


-- split type

split :: Mode -> Type -> Maybe (Type, Type)
split MSub (TArrow a b)
  | Just (b1, b2) <- split MSub b
  = Just (TArrow a b1, TArrow a b2)
split MSub (TArrow a b)
  | Just (a1, a2) <- split MSuper a
  = Just (TArrow a1 b, TArrow a2 b)
split m (TOp m' a b)
  | m == m'
  = Just (a, b)
split m (TOp m' a b)
  | Just (a1, a2) <- split m a
  = Just (TOp m' a1 b, TOp m' a2 b)
split m (TOp m' a b)
  | Just (b1, b2) <- split m b
  = Just (TOp m' a b1, TOp m' a b2)
  
split _ _ = Nothing


-- flip mode
flipmode :: Mode -> Mode
flipmode MSub = MSuper
flipmode MSuper = MSub


-- select type by mode
select :: Mode -> Type
select MSub   = TTop
select MSuper = TBot


-- subtyping


check :: Mode -> Type -> Type -> Bool -> Bool
check m _ t _
  | select m == t
  = True                                                                        -- S-top
check _ TInt TInt _ = True                                                      -- S-int
check m (TArrow a1 a2) (TArrow b1 b2) _                                         -- S-arr
  = (check (flipmode m) a1 b1 False) && (check m a2 b2 False)
check m a b _                                                                   -- S-and
  | Just (b1, b2) <- split m b
  = (check m a b1 False) && (check m a b2 False)
check m a b _                                                                   -- S-andl S-andr
  | Just (a1, a2) <- split m a
  = (check m a1 b False) || (check m a2 b False)
check m a b False = check (flipmode m) b a True                                 -- dual
check _ _ _ _ = False



-- Pretty printer
pretty :: Type-> String
pretty (TOp MSub a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOp MSuper a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Mode -> Type -> Type -> String
showtest MSub a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (check MSub a b False) 
showtest MSuper a b =
  pretty a ++ " :> " ++ pretty b ++ "  Result: " ++ show (check MSuper a b False) 
  

-- examples
t0 = TArrow TInt TInt

t1 = (TArrow (TInt) (TOp MSub TInt TInt))
test1 = showtest MSub t1 t1             -- True
test2 = showtest MSuper t1 t1           -- True

t2 = TArrow (TOp MSuper TInt t0) TInt
t3 = TOp MSub (TArrow t0 TInt) (TArrow TInt TInt)
test3 = showtest MSub t2 t3             -- True

test4 = showtest MSub TBot TInt         -- True
test5 = showtest MSuper (TArrow TInt TTop) t0   -- True
test6 = showtest MSuper TBot TInt         -- False
test7 = showtest MSub (TArrow TInt TTop) t0   -- False

test8 = showtest MSub (TOp MSub t0 TInt) (TOp MSub t0 TInt) -- True
test9 = showtest MSuper (TOp MSub t0 TInt) (TOp MSub t0 TInt) -- True
test8 = showtest MSub (TOp MSuper t0 TInt) (TOp MSuper t0 TInt) -- True
test8 = showtest MSuper (TOp MSuper t0 TInt) (TOp MSuper t0 TInt) -- True
