module Jat.Program.Parser (
  fromString
  )
where

import Jat.Program.Data

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import qualified Data.Map as M
import qualified Data.Array as A
import Control.Monad (liftM)

fromString :: String -> Program
fromString input = case parse parseProgram "" input of
  Left err   -> error $ "parse error: " ++ show err
  Right prog -> prog


lexer :: T.TokenParser ()
lexer = T.makeTokenParser emptyDef {
    T.identStart    = letter
  , T.identLetter   = alphaNum <|> oneOf "_"
  , T.reservedNames = [
        "int"   , "bool"  , "void"
      , "true"  , "false" , "unit" , "null"
      , "class"
      ]
  , T.caseSensitive = False
  , T.commentLine   = "//"
  }

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer
identifier :: Parser String
identifier = T.identifier lexer
integer    :: Parser Integer
integer    = T.integer lexer
reserved   :: String -> Parser ()
reserved   = T.reserved lexer
symbol     :: String -> Parser String
symbol     = T.symbol lexer
colon      :: Parser String
colon      = T.colon lexer

int :: Parser Int
int = do
  i <- integer
  return (fromIntegral i)
  <?> "parser:int" 

parseProgram :: Parser Program
parseProgram = do
  whiteSpace
  cs <- parseClassPool
  return $ P cs
  <?> "parser:program"

parseClassPool ::Parser ClassPool
parseClassPool = do
  cs <- many parseClass
  return $ M.fromList cs
  <?> "parsearser:classpool"

parseClass :: Parser (ClassId, Class)
parseClass = do
  symbol "Class:"
  symbol "Name:"
  cname <- identifier
  symbol "Classbody:"
  symbol "Superclass:"
  super' <- identifier <|> symbol "<None>"
  let super = if super' /= "<None>" then Just super' else Nothing
  fpool <- parseFieldPool
  mpool <- parseMethodPool
  return (ClassId cname, Class (ClassId cname) (ClassId `liftM` super) fpool mpool undefined undefined undefined)
  <?> "parser:class"

parseFieldPool :: Parser FieldPool
parseFieldPool = do
  symbol "Fields:"
  fs <- many $ try parseField
  return $ M.fromList fs
  <?> "parser:fieldpool"

parseField :: Parser (FieldId, Field)
parseField = do
  ftype <- parseType
  fname <- identifier
  return (FieldId fname, Field (FieldId fname) ftype) 
  <?> "parser:field"

parseMethodPool ::Parser MethodPool
parseMethodPool = do
  symbol "Methods:"
  ms <- many parseMethod
  return $ M.fromList ms
  <?> "parser:methodpool"

parseMethod :: Parser (MethodId, Method)
parseMethod = do
  symbol "Method:" 
  mreturn <- parseType
  mname <- identifier 
  mparams <- parseParams
  symbol "Methodbody:"
  symbol "MaxStack:"
  mxs <- int 
  symbol "MaxVars:"
  mxl <- int
  mins <- parseBytecode
  let minsa = A.listArray (0,length mins - 1) mins
  return (MethodId mname, Method (MethodId mname) mparams mreturn mxs mxl minsa)
  <?> "parser:method"

parseParams :: Parser [Type]
parseParams = do 
  symbol "Parameters:"
  {-many $ try (parseType >> notFollowedBy colon) >> parseType-}
  let p = parseType >>= \tp -> identifier >> return tp
  many $ try p
  <?> "parser:parameters"

parseType :: Parser Type
parseType = do
  reserved "int"
  return IntType
  <|> do
  reserved "bool"
  return BoolType
  <|> do
  reserved "null"
  return NullType
  <|> do
  reserved "void"
  return Void
  <|> do
  c <- identifier
  return $ RefType (ClassId c)
  <?> "parser:type"

parseBytecode :: Parser [Instruction]
parseBytecode = do
  symbol "Bytecode:"
  many parseInstruction
  <?> "parsearser:bytecode"

parseInstruction :: Parser Instruction
parseInstruction = do
  integer 
  colon
  instruction'
  <?> "instruction"
  where 
    instruction' = do
      try $ symbol "Load"
      i <- int
      return $ Load i
      <|> do
      try $ symbol "Store"
      i <- int
      return $ Store i 
      <|> do
      try $ symbol "Push"
      v <- parseValue
      return $ Push v
      <|> do
      try $ symbol "New"
      cn <- identifier
      return $ New (ClassId cn)
      <|> do
      try $ symbol "Getfield"
      fn <- identifier
      cn <- identifier
      return $ GetField (FieldId fn) (ClassId cn)
      <|> do
      try $ symbol "Putfield"
      fn <- identifier
      cn <- identifier
      return $ PutField (FieldId fn) (ClassId cn)
      <|> do
      try $ symbol "Checkcast"
      cn <- identifier
      return $ CheckCast (ClassId cn)
      <|> do
      try $ symbol "Invoke"
      mn <- identifier
      i  <- int
      return $ Invoke (MethodId mn) i 
      <|> do
      try $ symbol "Return"
      return Return 
      <|> do
      try $ symbol "Pop"
      return Pop
      <|> do
      try $ symbol "IAdd"
      return IAdd
      <|> do
      try $ symbol "ISub"
      return ISub
      <|> do
      try $ symbol "CmpGeq"
      return ICmpGeq
      <|> do
      try $ symbol "Goto"
      i <- int
      return $ Goto i
      <|> do
      try $ symbol "IfFalse"
      i <- int
      return $ IfFalse i 
      <|> do
      try $ symbol "CmpEq"
      return CmpEq
      <|> do
      try $ symbol "CmpNeq"
      return CmpNeq
      <|> do
      try $ symbol "CmpEq"
      return CmpEq
      <|> do
      try $ symbol "BNot"
      return BNot
      <|> do
      try $ symbol "BAnd"
      return BAnd
      <|> do
      try $ symbol "BOr"
      return BOr

parseValue :: Parser Value
parseValue = do
  i <- int
  return $ IntVal i
  <|> do 
  reserved "true"
  return $ BoolVal True
  <|> do
  reserved "false"
  return $ BoolVal False
  <|> do
  reserved "null"
  return Null
  <|> do
  reserved "unit"
  return Unit
  <?> "value"

 

