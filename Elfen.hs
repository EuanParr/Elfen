module Elfen where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Char as Char
import qualified Data.Maybe as Maybe
import qualified System.IO

{-
Lexical/static scope seems a good idea but Lisp complicates things
Dynamic scope is easy - just have memory map each symbol to a value
For lexical scope, different occurrences of symbols must be mapped to different values at any one time
-}

type Address = Integer

type Environment = Map.Map Symbol Address

type Memory = ((Map.Map Address Value), Integer)

data Constant =
    Character Char
  | Integer Integer

instance Show Constant where
  show (Character c) = [c]
  show (Integer n) = show n

type Symbol = String

data Value =
    Symbol Symbol
  | Cons Value Value
  | Nil
  | Constant Constant
  | Abstraction Value [Symbol] Environment
  | Primitive Primitive

instance Show Value where
  show (Symbol s) = s
  show c@(Cons _ _) = showList' c
  show Nil = showList' Nil
  show (Constant c) = show c
  show (Abstraction _ _ _) = "<Abstraction>"
  show (Primitive p) = "<Primitive " ++ show p ++ ">"

showList' :: Value -> String
showList' v = '(' : f v
 where f Nil = ")"
       f (Cons x y@(Cons _ _)) = show x ++ " " ++ f y
       f (Cons x y) = show x ++ f y
       f x = " . " ++ show x ++ ")" 

newtype MemUser a = Mu {mu :: (Memory -> (a, Memory))}

instance Functor MemUser where
  fmap = Monad.liftM

instance Applicative MemUser where
  pure x = Mu (\m -> (x, m))
  (<*>) = Monad.ap 

instance Monad MemUser where
  (Mu mx) >>= mf = Mu (\m -> let (a, m') = mx m in mu (mf a) m')
--return = pure

{-
return a >>= k
= Mu (\m -> (a, m)) >>= k
= Mu (\m -> let (b, m') = (\m -> (a, m)) m in mu (k b) m')
= Mu (\m -> let (b, m') = (a, m) in mu (k b) m')
= Mu (\m -> mu (k a) m)
= Mu (mu (k a))
= k a

(Mu mx) >>= return
= Mu (\m -> let (a, m') = mx m in mu (return a) m')
= Mu (\m -> let (a, m') = mx m in mu (Mu (\n -> (a, n))) m')
= Mu (\m -> let (a, m') = mx m in (\n -> (a, n)) m')
= Mu (\m -> let (a, m') = mx m in (a, m'))
= Mu (\m -> mx m)
= Mu mx

(Mu mx) >>= (\x -> k x >>= h)
= Mu (\m -> let (a, m') = mx m in mu ((\x -> k x >>= h) a) m')
= Mu (\m -> let (a, m') = mx m in mu (k a >>= h) m')
= Mu (\m -> let (a, m') = mx m in mu (Mu (\n -> let (b, n') = mu (k a) n in mu (h b) n')) m')
= Mu (\m -> let (a, m') = mx m in (\n -> let (b, n') = mu (k a) n in mu (h b) n') m')
= Mu (\m -> let (a, m') = mx m in (let (b, n') = mu (k a) m' in mu (h b) n'))
= Mu (\m -> (let (b, n') = mu (k (fst $ mx m)) (snd $ mx m) in mu (h b) n'))
= Mu (\m -> mu (h (fst $ mu (k (fst $ mx m)) (snd $ mx m))) (snd $ mu (k (fst $ mx m)) (snd $ mx m))))
= Mu (\m -> let (a, m') = mu (k (fst $ mx m)) (snd % mx m) in mu (h a) m')
= Mu (\m -> let (a, m') = (let (b, n') = mx m in mu (k b) n') in mu (h a) m')
= Mu (\m -> let (a, m') = (\n -> let (b, n') = mx n in mu (k b) n') m in mu (h a) m')
= Mu (\n -> let (b, n') = mx n in mu (k b) n') >>= h
= ((Mu mx) >>= k) >>= h
-}

setVal :: Value -> Address -> MemUser ()
setVal x a = Mu (\(m, n) -> ((), (Map.insert a x m, n)))

getVal :: Address -> MemUser Value
getVal a = Mu (\(m, n) -> ((Map.!) m a, (m, n)))

freshAddress :: MemUser Address
freshAddress = Mu (\(m, n) -> (n, (m, n+1)))

bind :: Symbol -> Address -> Environment -> Environment
bind s a e = Map.insert s a e

getAddr :: Symbol -> Environment -> Address
getAddr s e = (Map.!) e s

eval :: Value -> Environment -> MemUser Value
eval (Symbol s) e = getVal $ getAddr s e
eval (Cons x y) e = evalApplication x y e
eval Nil _ = pure Nil
eval (Constant c) _ = pure (Constant c)
eval _ _ = error "Evaluating an applicable value outside of an application"

evalApplication :: Value -> Value -> Environment -> MemUser Value
evalApplication (Symbol x) y e -- check for special forms
 | Map.member x specialOperators = (Map.!) specialOperators x y e
evalApplication x y e = do
  x' <- eval x e
  y' <- evalList y e
  apply x' y'

evalList :: Value -> Environment -> MemUser [Value]
evalList Nil _ = pure []
evalList (Cons x y) e = do
  x' <- eval x e
  y' <- evalList y e
  pure (x' : y')
evalList _ _ = error "Evaluating a non-list as a list"

apply :: Value -> [Value] -> MemUser Value
apply (Primitive x) ys = applyPrimitive x ys
apply (Abstraction x ss e) ys = (defineList (matchingZip ss ys) e) >>= \e' -> eval x e'
  where matchingZip [] [] = []
        matchingZip (x':xs') (y':ys') = (x', y') : matchingZip xs' ys'
        matchingZip _ _ = error "different number of arguments and parameters"
apply _ _ = error "Applying a non-applicable value"

-- give a symbol a new address binding and set it to a value
define :: Symbol -> Value -> Environment -> MemUser Environment
define s x e = do
  a <- freshAddress
  setVal x a
  pure $ bind s a e

defineList :: [(Symbol, Value)] -> Environment -> MemUser Environment
defineList [] e = pure e
defineList ((x, y):zs) e = do
  e' <- define x y e
  defineList zs e'

data Primitive = CONS | CF | CS
 | PLUS | MINUS deriving Show

applyPrimitive :: Primitive -> [Value] -> MemUser Value
applyPrimitive CONS [x,y] = pure $ Cons x y
applyPrimitive CF [Cons x _] = pure $ x
applyPrimitive CS [Cons _ y] = pure $ y
applyPrimitive PLUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x + y)
applyPrimitive MINUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x - y)
applyPrimitive _ _ = error "Wrong argument type (s) for primitive operator"
 
{- I pick out special operators at symbol level rather than value level - it will not be possible to evaluate anything but some predetermined symbols into special operators, which is in accordance with typical Lisps and will make checking easier (it's hard to imagine what type a special operator might have). -}
specialOperators :: Map.Map Symbol (Value -> Environment -> MemUser Value)
specialOperators = Map.fromList
                   [("quote", (\(Cons v _) _ -> pure v)),
                    ("proc", (\(Cons params (Cons body Nil)) e -> pure (Abstraction body (map asSymbol $ unElfenList params) e)))]

unElfenList :: Value -> [Value]
unElfenList Nil = []
unElfenList (Cons x xs) = x: unElfenList xs

asSymbol :: Value -> Symbol
asSymbol (Symbol s) = s

initialState :: (Environment, Memory)
initialState = mu (defineList initialDefinitions Map.empty) (Map.empty, 0)
 where initialDefinitions =
         [("+", Primitive PLUS)]

evalSequential :: [Value] -> Environment -> MemUser [Value]
evalSequential [] _ = pure []
evalSequential (x:y) e = do
  x' <- eval x e
  y' <- evalSequential y e
  pure (x' : y')

enterEval :: [Value] -> [Value]
enterEval vs = let (initialEnv, initialMem) = initialState in
  fst $ mu (evalSequential vs initialEnv) initialMem

data Token = LeftParenthesis | RightParenthesis
  | SymbolLiteral String
  | StringLiteral String
  | IntegerLiteral Integer
  | Apostrophe deriving Show

tokenise :: String -> [Token]
tokenise [] = []
tokenise ('(':cs) = LeftParenthesis : tokenise cs
tokenise (')':cs) = RightParenthesis : tokenise cs
tokenise ('\'':cs) = Apostrophe : tokenise cs
tokenise (c:cs)
  | Char.isSpace c = tokenise cs
  | Char.isDigit c = let (n, cs') = tokeniseInteger (c:cs) in IntegerLiteral n : tokenise cs'
tokenise ('-':c:cs)
  | Char.isDigit c = let (n, cs') = tokeniseInteger (c:cs) in IntegerLiteral (-n) : tokenise cs'
tokenise ('"':cs) = let (s, cs') = tokeniseString cs in StringLiteral s : tokenise cs'
tokenise cs = let (s, cs') = tokeniseSymbol cs in SymbolLiteral s : tokenise cs'

tokeniseInteger :: String -> (Integer, String)
tokeniseInteger = f 0
  where f acc (c:cs)
          | Char.isDigit c = f (acc * 10 + (toInteger $ Char.digitToInt c)) cs
          | otherwise = (acc, c:cs)

tokeniseString :: String -> (String, String)
tokeniseString cs = let (s, cs') = break (== '"') cs in (s, tail cs')

tokeniseSymbol :: String -> (String, String)
tokeniseSymbol = break (\c -> Char.isSpace c || c == '(' || c == ')')

parseVal :: [Token] -> Maybe (Value, [Token])
parseVal [] = Nothing
parseVal (LeftParenthesis:ts) = parseList ts
parseVal (RightParenthesis:_) = Nothing
parseVal (SymbolLiteral s : ts) = Just (Symbol s, ts)
parseVal (StringLiteral s : ts) = Just (elfenString s, ts)
parseVal (IntegerLiteral s : ts) = Just (Constant (Integer s), ts)
parseVal (Apostrophe : ts) = case parseVal ts of
                               Nothing -> Nothing
                               Just (v, ts') -> Just (Cons (Symbol "quote") (Cons v Nil), ts')

parseList :: [Token] -> Maybe (Value, [Token])
parseList (RightParenthesis:ts) = Just (Nil, ts)
parseList ts = case parseVal ts of
                Nothing -> Nothing
                Just (v, ts') ->
                  case parseList ts' of
                    Nothing -> Nothing
                    Just (v', ts'') -> Just (Cons v v', ts'')

elfenString :: String -> Value
elfenString = foldr Cons Nil . map (Constant . Character)

parse :: [Token] -> Maybe [Value]
parse [] = Just []
parse ts = case parseVal ts of
             Nothing -> Nothing
             Just (v, ts') ->
               case parse ts' of
                 Nothing -> Nothing
                 Just vs -> Just $ v:vs



processFile :: System.IO.Handle -> IO ()
processFile h = do
  ts <- System.IO.hGetContents h
  putStrLn $ unlines $ map show $ enterEval $ Maybe.fromMaybe [Nil] $ parse $ tokenise ts

main :: IO ()
main = do
  i <- getLine
  System.IO.withFile i System.IO.ReadMode processFile
