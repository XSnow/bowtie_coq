data Mode = MSub | MSuper
          deriving (Eq, Show)
          
data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TOp Mode Type Type -- And for MSub, Or for MSuper
          deriving (Eq, Show)


-- split type

split :: Mode -> Type -> Maybe (Type, Type)
split MSub (TArrow a b) =
  case (split MSub b) of
  Just (b1, b2) -> Just (TArrow a b1, TArrow a b2)
  _ -> do
    (a1, a2) <- split MSuper a
    return (TArrow a1 b, TArrow a2 b)
split m (TOp m' a b) =
  | m == m'   = Just (a, b)
  | otherwise = case (split m a) of
                         Just (a1, a2) -> Just (TOp m' a1 b, TOp m' a2 b)
                         _             -> do
                                          (b1, b2) <- split MSub b
                                          return (TOp m' a b1, TOp m' a b2)
split _ _ = Nothing


-- flip mode
flipmode :: Mode -> Mode
flipmode MSub = MSuper
flipmode MSuper = MSub


-- subtyping

check :: Mode -> Type -> Type -> Bool
check MSub _ TTop    = True
check MSuper TBot _  = True
check _ TInt TInt    = True
check m a b          =
  case (split m b) of
    Just (b1, b2) -> (check m a b1) && (check m a b2) -- rule S-and
    _             -> case (split (flipmode m) a) of
                       Just (a1, a2) -> (check m a1 b) && (check m a2 b)
                       _             -> case (split m a) of
                                          Just (a1, a2) -> (check m a1 b) || (check m a2 b)
                                          _ -> case (split (flipmode m) b) of
                                                 Just (b1, b2) -> (check m a b1) || (check m a b2)
                                                 _ -> case (a, b) of
                                                        (TArrow a1 a2, TArrow b1 b2) -> (check (flipmode m) a1 b1) && (check m a2 b2)
                                                        _ -> False

-- check True m a b = check False (flipmode m) b a


-- Pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOr a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Mode -> Type -> Type -> String
showtest MSub a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (check MSub a b) 
showtest MSuper a b =
  pretty a ++ " :> " ++ pretty b ++ "  Result: " ++ show (check MSuper a b) 
  

-- examples
t0 = TArrow TInt TInt

t1 = (TArrow (TInt) (TAnd TInt TInt))
test1 = showtest MSub t1 t1
test2 = showtest MSuper t1 t1

t2 = TArrow (TOr TInt t0) TInt
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)
test3 = showtest MSub t2 t3
