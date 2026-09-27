{-# language BlockArguments, LambdaCase, MultilineStrings, ViewPatterns #-}

module Main where

import Control.Applicative
import Control.Monad
import Data.Char
import Data.Foldable
import Data.Set (Set)
import Data.Set qualified as Set
import Text.Show.Pretty (pPrint)


-- Errors & rendering
--------------------------------------------------------------------------------

type Recovery = Set Char
type Msg      = String
type Pos      = String
data Error    = Error Msg Pos Pos Pos

instance Show Error where
  show (Error msg s s' s'') =
    let l   = length s
        l'  = length s'
        l'' = length s''
    in show (msg, take (l - l') s, take (l' - l'') s')

highlight :: String -> [(Pos, Pos, Pos)] -> String
highlight s es = let
  len = length s

  posToInt :: Pos -> Int
  posToInt s = len - length s

  (errSpans :: Set Int, errPoss :: Set Int) = foldl'
    (\(!errSpans, !errPoss) (posToInt -> i, posToInt -> j, posToInt -> k) ->
       ( foldl' (flip Set.insert) errSpans [i..k-1]
       , Set.insert j errPoss))
    mempty es

  -- extend the end to allow the end position to be rendered
  s' = s ++ " "

  errString :: String
  errString = do
    (i, c) <- zip [0..] s'
    if c == '\n' then
      if Set.member i errPoss then
        "^\n"
      else
        "\n"
    else if Set.member i errPoss then
      "^"
    else if Set.member i errSpans then
      "─"
    else
      " "

  in unlines do
       (l, err) <- zip (lines s') (lines errString)
       if all (==' ') err then
         pure l
       else
         pure $ l ++ "\n" ++ err


-- Parser library
--------------------------------------------------------------------------------

data Res a
  = OK a String
  | Err Msg Pos Pos Pos
  | Fail
  deriving (Show, Functor)

newtype Parser a = Parser {runParser :: Recovery -> String -> Res a}
  deriving Functor

instance Applicative Parser where
  pure a = Parser \r s -> OK a s
  (<*>) = ap

instance Monad Parser where
  return = pure
  Parser f >>= g = Parser \r s -> case f r s of
    OK a s           -> runParser (g a) r s
    Err msg s s' s'' -> Err msg s s' s''
    Fail             -> Fail

instance Alternative Parser where
  empty = Parser \_ _ -> Fail
  Parser f <|> Parser g = Parser \r s -> case f r s of
    Fail -> g r s
    res  -> res

recover :: Recovery -> String -> (String, String)
recover r s = go s s where
  go stripped (c:s)
    | Set.member c r = (stripped, c:s)
    | isSpace c      = go stripped s
    | otherwise      = go s s
  go stripped [] = (stripped, [])

instance MonadFail Parser where
  fail msg = Parser \r s0 -> case recover r s0 of
    (s1, s2) -> Err msg s0 s1 s2

class EmbedError a where
  mkError :: Maybe a -> Error -> a

mustFollow :: EmbedError a => [Char] -> Parser a -> Parser (a, Char)
mustFollow cs p = Parser \r s0 ->
  let cSet = Set.fromList cs in
  let r'   = r <> cSet in
  case runParser p r' s0 of
    OK a s1
      | c:s2 <- s1, Set.member c cSet ->
        OK (a, c) s2
      | (s2, s3) <- recover r' s1 ->
        case s3 of
          c:s4 | Set.member c cSet ->
            OK (mkError (Just a) (Error cs s1 s1 s2), c) s4
          s3 ->
            Err ("expected one of " ++ show cs) s1 s2 s3
    Err msg s1 s2 s3
      | c:s4 <- s3, Set.member c cSet ->
        OK (mkError Nothing (Error cs s0 s1 s2), c) s4
      | otherwise ->
        Err msg s1 s2 s3
    Fail -> Fail

mayFollow :: EmbedError a => [Char] -> Parser a -> Parser (Either (a, Char) a)
mayFollow cs p = Parser \r s0 ->
  let cSet = Set.fromList cs in
  let r'   = r <> cSet in
  case runParser p r' s0 of
    OK a s1
      | c:s2 <- s1, Set.member c cSet ->
        OK (Left (a, c)) s2
      | otherwise ->
        OK (Right a) s1
    Err msg s1 s2 s3
      | c:s4 <- s3, Set.member c cSet ->
        OK (Left (mkError Nothing (Error msg s0 s1 s2), c)) s4
      | otherwise ->
        OK (Right (mkError Nothing (Error msg s0 s1 s2))) s3
    Fail -> Fail

eofMustFollow :: EmbedError a => Parser a -> Parser a
eofMustFollow p = Parser \r s0 -> case runParser p r s0 of
  OK a "" -> OK a ""
  OK a s1 -> case recover mempty s1 of
    (s2, _) -> OK (mkError (Just a) (Error "expected end of input" s1 s1 s2)) ""
  Err msg s1 s2 "" -> OK (mkError Nothing (Error msg s0 s1 s2)) ""
  Err msg s1 s2 s3 -> case recover mempty s3 of
    (s4, _) -> OK (mkError Nothing (Error msg s0 s2 s4)) ""
  Fail -> OK (mkError Nothing (Error "unknown parse error" s0 s0 "")) ""

satisfy' :: (Char -> Bool) -> Parser Char
satisfy' f = Parser \r -> \case
  c:s | f c -> OK c s
  _ -> Fail

char' :: Char -> Parser ()
char' c = () <$ satisfy' (==c)


-- Lexing, combinator shorthands
--------------------------------------------------------------------------------

ws'    = () <$ many (satisfy' isSpace)
sym' c = char' c <* ws'
name'  = satisfy' (\c -> isLower c && c /= 'λ') <* ws'

infixl 6 <!
(<!) :: EmbedError a => Show a => Parser a -> Char -> Parser a
(<!) p c = fst <$> (mustFollow [c] p <* ws')

infixl 6 <?
(<?) :: EmbedError a => Parser a -> Char -> Parser (Either a a)
(<?) p c = either (Left . fst) Right <$> (mayFollow [c] p <* ws')

infixl 6 <|
(<|) :: EmbedError a => Parser a -> Parser a
(<|) p = either fst id <$> (mayFollow [] p <* ws')


-- The AST types
--------------------------------------------------------------------------------

data Ident_ e
  = Ident Char
  | IdentError (Maybe (Ident_ e)) e
  deriving (Show, Functor, Foldable, Traversable)

data Tm_ e
  = Var (Ident_ e)
  | App (Tm_ e) (Tm_ e)
  | Plus (Tm_ e) (Tm_ e)
  | Mul (Tm_ e) (Tm_ e)
  | List [Tm_ e]
  | Let (Ident_ e) (Tm_ e) (Tm_ e)
  | Lam (Ident_ e) (Tm_ e)
  | TmError (Maybe (Tm_ e)) e
  deriving (Show, Functor, Foldable, Traversable)

type Tm = Tm_ Error
type Ident = Ident_ Error

instance EmbedError Tm    where mkError = TmError
instance EmbedError Ident where mkError = IdentError
instance EmbedError ()    where mkError = \_ _ -> ()


-- The parser
--------------------------------------------------------------------------------

ident' = Ident <$> name'
ident  = ident' <|> fail "identifier"

atom' = (Var <$> ident')
    <|> (sym' '(' *> tm <! ')')
    <|> (sym' '[' *> pure (List []) <* sym' ']')
    <|> (sym' '[' *> (List <$> nonEmptyList) <! ']')

atom = atom' <|> fail "atomic expression"

nonEmptyList =
  (tm <? ',') >>= \case
    Left t  -> (t:) <$> nonEmptyList
    Right t -> pure [t]

goSpine t =
      (do u <- (atom' <|); goSpine (App t u))
  <|> pure t

spine = goSpine =<< atom

-- left-associative
goMul t =
  (spine <? '*') >>= \case
    Left u  -> goMul (Mul t u)
    Right u -> pure (Mul t u)

mul =
  (spine <? '*') >>= \case
    Left t  -> goMul t
    Right t -> pure t

-- right-associative
plus =
  (mul <? '+') >>= \case
    Left t  -> Plus t <$> plus
    Right t -> pure t

tm :: Parser Tm
tm =
      (Lam <$> ((sym' 'λ' <|> sym' '\\') *> ident <! '.') <*> (tm <|))
  <|> (Let <$> (sym' 'L' *> ident <! '=') <*> (tm <! ';') <*> (tm <|))
  <|> plus


-- Testing
--------------------------------------------------------------------------------

parse :: String -> Tm
parse s = case runParser (ws' *> eofMustFollow tm) mempty s of
  OK a _ -> a
  _      -> error "impossible"

testParser :: String -> IO ()
testParser s = pPrint $ parse s

testHighlight :: String -> IO ()
testHighlight s = do
  let errors =
        map (\(Error _ s s' s'') -> (s, s', s'')) $
        toList $ parse s
  putStr $ highlight s errors

src :: String
src =
  """
  L e a b = λ f. λ y. f y y ( ?  ?  y;
  L b = [x, y, z, ?? + x * ?? + x, ((), k];
  L f = λ x. λ y  ? ;
  [a, b, c, λλλλλ]
  """

main :: IO ()
main = testHighlight src
