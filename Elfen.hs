module Elfen where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import qualified Data.Maybe as Maybe
import qualified System.IO
import qualified System.Environment

{-
Lexical/static scope seems a good idea but Lisp complicates things
Dynamic scope is easy - just have memory map each symbol to a value
For lexical scope, different occurrences of symbols must be mapped to different values at any one time
-}

type Environment = Map.Map Symbol Value

data Constant =
    Character Char
  | Integer Integer deriving Eq

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
  | Primitive Primitive deriving Eq

instance Show Value where
  show (Symbol s) = s
  show c@(Cons _ _) = showList' c
  show Nil = showList' Nil
  show (Constant c) = show c
  show (Abstraction v ss e) = "<Abstraction " ++ show ss ++ " " ++ show v ++ ">"  
  show (Primitive p) = "<Primitive " ++ show p ++ ">"

showList' :: Value -> String
showList' v = '(' : f v
 where f Nil = ")"
       f (Cons x y@(Cons _ _)) = show x ++ " " ++ f y
       f (Cons x y) = show x ++ f y
       f x = " . " ++ show x ++ ")"

-- identity monad for now
newtype M a = Mu {mu :: a}

instance Functor M where
  fmap = Monad.liftM

instance Applicative M where
  pure x = Mu x
  (<*>) = Monad.ap 

instance Monad M where
  (Mu mx) >>= mf = mf mx
--return = pure

{-
return a >>= k
= Mu a >>= k
= k a

(Mu mx) >>= return
= return mx
= Mu mx

(Mu mx) >>= (\x -> k x >>= h)
= (\x -> k x >>= h) mx
= k mx >>= h
= ((Mu mx) >>= k) >>= h
-}



bind :: Symbol -> Value -> Environment -> Environment
bind s v e = Map.insert s v e

eval :: Value -> Environment -> M Value
eval (Symbol s) e = pure $ (Map.findWithDefault) (error $ "Symbol has no definition: " ++ show s) s e
eval (Cons x y) e = evalApplication x y e
eval Nil _ = pure Nil
eval (Constant c) _ = pure (Constant c)
eval _ _ = error "Evaluating an applicable value outside of an application"

evalApplication :: Value -> Value -> Environment -> M Value
evalApplication (Symbol x) y e -- check for special forms
 | Map.member x specialOperators = (Map.!) specialOperators x y e
evalApplication x y e = do
  x' <- eval x e
  y' <- evalList y e
  apply x' y'

evalList :: Value -> Environment -> M [Value]
evalList Nil _ = pure []
evalList (Cons x y) e = do
  x' <- eval x e
  y' <- evalList y e
  pure (x' : y')
evalList _ _ = error "Evaluating a non-list as a list"

apply :: Value -> [Value] -> M Value
apply (Primitive x) ys = applyPrimitive x ys
apply a@(Abstraction x ss e) ys = (defineList (matchingZip ss ys) e) >>= \e' -> eval x e'
  where matchingZip [] [] = []
        matchingZip (x':xs') (y':ys') = (x', y') : matchingZip xs' ys'
        matchingZip _ _ = error $ "different number of arguments and parameters: " ++ show a ++ ", " ++ show ys
apply _ _ = error "Applying a non-applicable value"

-- give a symbol a new value binding
define :: Symbol -> Value -> Environment -> M Environment
define s v e = pure $ bind s v e

defineList :: [(Symbol, Value)] -> Environment -> M Environment
defineList [] e = pure e
defineList ((x, y):zs) e = do
  e' <- define x y e
  defineList zs e'

data Primitive = CONS | CF | CS
 | PLUS | MINUS | EQN | EQS | CONSP
 | Y deriving (Eq, Show)

applyPrimitive :: Primitive -> [Value] -> M Value
applyPrimitive CONS [x,y] = pure $ Cons x y
applyPrimitive CF [Cons x _] = pure $ x
applyPrimitive CS [Cons _ y] = pure $ y
applyPrimitive PLUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x + y)
applyPrimitive MINUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x - y)
applyPrimitive EQN [Constant (Integer x), Constant (Integer y)] = pure $ if x == y then Symbol "t" else Nil
applyPrimitive EQS [Symbol x, Symbol y] = pure $ if x == y then Symbol "t" else Nil
applyPrimitive CONSP [Cons _ _] = pure $ Symbol "t"
applyPrimitive CONSP _ = pure $ Nil
applyPrimitive o vs = error $ "Wrong argument type (s) for primitive operator: " ++ show o ++ " of " ++ show vs
 
{- I pick out special operators at symbol level rather than value level - it will not be possible to evaluate anything but some predetermined symbols into special operators, which is in accordance with typical Lisps and will make checking easier (it's hard to imagine what type a special operator might have). -}
specialOperators :: Map.Map Symbol (Value -> Environment -> M Value)
specialOperators = Map.fromList
                   [("quote", (\(Cons v _) _ -> pure v)),
                    ("lam", (\(Cons params (Cons body Nil)) e -> pure (Abstraction body (map asSymbol $ unElfenList params) e))),
                    ("if", (\(Cons test (Cons true (Cons false Nil))) e -> eval test e >>= (\r -> if r == Nil then eval false e else eval true e))),
                    ("letrec1", fixOperator),
                    ("letrec2", fixOpTwo),
                    ("letrec", mutualFixOperator),
                    ("apply", (\(Cons f (Cons xs Nil)) e -> eval f e >>= \f' -> evalList xs e >>= \xs' -> apply f' xs'))]

fixOperator :: Value -> Environment -> M Value
fixOperator (Cons (Cons s (Cons v Nil)) (Cons body Nil)) e = do
  openDef <- eval (elfenList [Symbol "lam", elfenList [s], v]) e
  recursiveV <- apply yFunction [openDef]
  e' <- define (asSymbol s) recursiveV e
  eval body e'

fixOpTwo :: Value -> Environment -> M Value
fixOpTwo (Cons (Cons s (Cons v (Cons s' (Cons v' Nil)))) (Cons body Nil)) e = do
  openDef <- pure (elfenList [Symbol "lam", elfenList [s, s'], v])
  openDef' <- pure (elfenList [Symbol "lam", elfenList [s, s'], v'])
  listDef <- eval (elfenList [Symbol "lam", elfenList [Symbol "self"], elfenList [Symbol "cons", elfenList [openDef, elfenIndexer 0 (Symbol "self"), elfenIndexer 1 (Symbol "self")], elfenList [Symbol "cons", elfenList [openDef', elfenIndexer 0 (Symbol "self"), elfenIndexer 1 (Symbol "self")], Nil]]]) e
  recursiveV <- apply yFunction [listDef]
  rv <- apply (Primitive CF) [recursiveV]
  rv'' <- apply (Primitive CS) [recursiveV]
  rv' <- apply (Primitive CF) [rv'']
  e' <- define (asSymbol s) rv e
  e'' <- define (asSymbol s') rv' e'
  eval body e''

elfenIndexer :: Integer -> Value -> Value
elfenIndexer n v = elfenList [Symbol "cf", f n v]
  where f 0 v = v
        f n v = elfenList [Symbol "cs", f (n-1) v]

{-
from https://okmij.org/ftp/Computation/fixed-point-combinators.html
(\l -> Y (\self -> map ($ self) l)) [f, g, h]
= Y (\self -> map ($ self) [f, g, h])
= Y (\self -> [f self, g self, h self])
= (\self -> [f self, g self, h self]) (Y (\self -> [f self, g self, h self]))
= [f (Y (\self -> [f self, g self, h self])), g (Y (\self -> [f self, g self, h self])), h (Y (\self -> [f self, g self, h self]))]
-}
mutualFixOperator :: Value -> Environment -> M Value
mutualFixOperator (Cons defs (Cons body Nil)) e =
  let ds' = pairUp $ unElfenList defs in
    let ss = map fst ds' in
      let openDefs = zipWith (\(s, v) n -> (n, s, elfenList [(Symbol "lam"), (elfenList ss), v])) ds' [0..] in
        let aps = map (\(n, s, v) -> elfenList (v : map (\n' -> elfenIndexer n' (Symbol "self")) [0..(toInteger $ length ss - 1)])) openDefs in do
          listDef <- eval (elfenList [Symbol "lam", elfenList [Symbol "self"], elfenListMaker aps]) e
          recursiveV <- apply yFunction [listDef]
          results <- mapM (\(n, _, _) -> Foldable.foldrM (\_ v -> apply (Primitive CS) [v]) recursiveV [1..n] >>= (\v -> apply (Primitive CF) [v])) openDefs
          e' <- defineList (zip (map asSymbol ss) results) e
          eval body e'
          --pure $ elfenList results

unElfenList :: Value -> [Value]
unElfenList Nil = []
unElfenList (Cons x xs) = x: unElfenList xs

elfenList :: [Value] -> Value
elfenList (v:vs) = Cons v $ elfenList vs
elfenList [] = Nil

elfenListMaker :: [Value] -> Value
elfenListMaker (v:vs) = elfenList [Symbol "cons", v, elfenListMaker vs]
elfenListMaker [] = Nil

pairUp :: [a] -> [(a, a)]
pairUp (x:y:xs) = (x,y) : pairUp xs
pairUp [] = []

asSymbol :: Value -> Symbol
asSymbol (Symbol s) = s

initialState :: Environment
initialState = mu (defineList initialDefinitions Map.empty)
 where initialDefinitions =
         [("+", Primitive PLUS),
          ("eqn", Primitive EQN),
          ("eqs", Primitive EQS),
          ("consp", Primitive CONSP),
          ("t", Symbol "t"),
          ("nil", Nil),
          ("Y", yFunction),
          ("cons", Primitive CONS),
          ("cf", Primitive CF),
          ("cs", Primitive CS),
          ("id", idFunction)]

yFunction :: Value
yFunction = let yPart = elfenList [Symbol "lam", elfenList [Symbol "x"], elfenList [Symbol "f", elfenList [Symbol "x", Symbol "x"]]] in
  mu (eval (elfenList [Symbol "lam", elfenList [Symbol "f"], elfenList [yPart, yPart]]) (Map.empty))

idFunction :: Value
idFunction = Abstraction (Symbol "x") ["x"] Map.empty

evalSequential :: [Value] -> Environment -> M [Value]
evalSequential [] _ = pure []
evalSequential (x:y) e = do
  x' <- eval x e
  y' <- evalSequential y e
  pure (x' : y')

enterEval :: [Value] -> [Value]
enterEval vs = let initialEnv = initialState in
  mu (evalSequential vs initialEnv) 

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



processFile :: String -> IO ()
processFile ts =
  putStrLn $ unlines $ map show $ enterEval $ Maybe.fromMaybe [Nil] $ parse $ tokenise ts

main :: IO ()
main = do
  args <- System.Environment.getArgs
  if args == [] then {-getContents >>= processFile-} putStrLn "Error: no filename given." else System.IO.withFile (head args) System.IO.ReadMode (\h -> System.IO.hGetContents h >>= processFile)
