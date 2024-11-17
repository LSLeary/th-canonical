
-- --< Frontmatter >-- {{{

-- We test how `canonical` treats TH ASTs generated from unidiomatic Haskell.
-- As such, we quote some. Don't warn us about it.
{-# OPTIONS_GHC -Wno-unused-matches -Wno-name-shadowing #-}

-- We test how `canonical` treats almost every TH AST constructor.
-- As such, we quote GHC Haskell using the various extensions corresponding
-- to those constructors.
{-# LANGUAGE CPP, TemplateHaskell, TypeData, DataKinds, DefaultSignatures
           , PatternSynonyms, ViewPatterns, MultiWayIf, OverloadedLabels
           , MagicHash, UnboxedTuples, UnboxedSums, ImplicitParams
           , OverloadedRecordDot, ExplicitNamespaces
#-}

#if MIN_VERSION_GLASGOW_HASKELL(9,8,1,0)
{-# LANGUAGE TypeAbstractions #-}
#endif

-- base
import Data.Kind (Type)
import Data.Char (isSymbol)
import Data.Monoid (Sum(..))
import Data.Function (on)
import Data.Functor (($>))
import System.Exit (exitSuccess, exitFailure)

-- template-haskell
import Language.Haskell.TH.Ppr (Ppr, pprint)

-- th-canonical
import Language.Haskell.TH.Canonical (Canonical, canonical)

-- }}}

-- --< declarations >-- {{{

data Maybe_ a = Nothing_ | Just_ a

type String_ = String

class Show_ a where
  show_ :: a -> String_

class Foldable_ f where
  foldMap_ :: (a -> b) -> f a -> b

data List_ a = Nil_ | a :~ List_ a

(+~) :: Num a => a -> a -> a
(+~) = (+)
infixl 6 +~

data Bool_ = False_ | True_

type Integral_ = Integral

even_ :: Integral_ i => i -> Bool_
even_ i = case even i of
  False -> False_
  True  -> True_

type Applicative_ = Applicative

declarations :: IO (Sum Int, Sum Int)
declarations = foldMap (uncurry test)
  [ ( [d| f p1 p2 = b where b = (p1, p2) |]
    , [ "f a b = c where { c = (a, b) }"
      ]
    )
  , ( [d| Just_ x = y where y = Nothing_ |]
    , [ "Main.Just_ x = a"
      , " where { a = Main.Nothing_ }"
      ]
    )
  , ( [d| data Foo x y = Bar x y | Quux x deriving Show_ |]
    , [ "data Foo a b = Bar a b | Quux a"
      , "  deriving Main.Show_"
      ]
    )
  , ( [d| data Foo x where { Foo :: y -> Foo y } |]
    , [ "data Foo a where"
      , "  Foo :: forall a. a -> Foo a"
      ]
    )
  , ( [d| data Foo x where { Foo :: Maybe_ y -> Foo (Maybe_ y) } |]
    , [ "data Foo a where"
      , "  Foo :: forall a. (Main.Maybe_ a) -> Foo (Main.Maybe_ a)"
      ]
    )
  , ( [d| newtype Foo f x y = MkFoo (f y x) |]
    , [ "newtype Foo a b c = MkFoo (a c b)" ]
    )
  , ( [d| newtype Foo f x y = MkFoo { unFoo :: f y x } |]
    , [ "newtype Foo a b c = MkFoo { unFoo :: (a c b) }" ]
    )
  , ( [d| type data T x = A x | B (T x) |]
    , [ "type data T a = A a | B (T a)" ]
    )
  , ( [d| type T x = (x, x) |]
    , [ "type T a = (a, a)" ]
    )
  , ( [d| class Applicative_ f => Alt f where
            (<|>) :: f a -> f a -> f a
      |]
    , [ "class Main.Applicative_ a => Alt a where {"
      , "  (<|>) :: forall b. a b -> a b -> a b"
      , " }"
      ]
    )
  , ( [d| instance Show_ w => Show_ [w] where
            show_ = foldMap_ show_
      |]
    , [ "instance Main.Show_ a => Main.Show_ [a] where {"
      , "  Main.show_ = Main.foldMap_ Main.show_"
      , " }"
      ]
    )
  , ( [d| foldr :: (x -> y -> y) -> y -> List_ x -> y
          foldr   _   z  Nil_     = z
          foldr (|+|) z (x :~ xs) = x |+| foldr (|+|) z xs
      |]
    , [ "foldr _ a  (Main.Nil_)    = a"
      , "foldr a b ((Main.:~) c d) = a c (foldr a b d)"
      , "foldr :: forall a b. (a -> b -> b) -> b -> Main.List_ a -> b"
      ]
    )
  , ( [d| type Proxy :: k -> Type
          data Proxy = MkProxy
      |]
    , [ "data Proxy = MkProxy"
      , "type Proxy :: forall a. a -> *"
      ]
    )
  , ( [d| data family T x y z :: Type
          data instance T Bool_ (List_ y) z
            = Pair Bool_ (List_ y) | One z
      |]
    , [ "data family T a b c :: *"
      , "data instance forall a b. T Main.Bool_ (Main.List_ a) b"
      , "  = Pair Main.Bool_ (Main.List_ a) | One b"
      ]
    )
  , ( [d| data family T x y z :: Type
          newtype instance T Bool_ (List_ y) z = MkTIC (Bool_, List_ y, z)
      |]
    , [ "data family T a b c :: *"
      , "newtype instance forall a b. T Main.Bool_ (Main.List_ a) b"
      , "  = MkTIC (Main.Bool_, Main.List_ a, b)"
      ]
    )
  , ( [d| type family T x y z = (r :: Type) | r -> x y
          type instance T Bool_ (List_ y) z = (Bool_, List_ y, z)
      |]
    , [ "type instance forall a b. T Main.Bool_ (Main.List_ a) b"
      , "   = (Main.Bool_, Main.List_ a, b)"
      , "type family T a b c = (d :: *) | d -> a b"
      ]
    )
  , ( [d| type family Map (f :: k1 -> k2) (xs :: List_ k1) = (r :: List_ k2)
              | r -> f xs where
            Map _  Nil_     = Nil_
            Map f (x :~ xs) = f x :~ Map f xs
      |]
    , [ "type family Map (c :: a -> b) (d :: Main.List_ a)"
      , "  = (e :: Main.List_ b) | e -> c d"
      , " where"
      , "  Map _ 'Main.Nil_ = 'Main.Nil_"
      , "  forall f g h. Map f ('(Main.:~) g h) = '(Main.:~) (f g) (Map f h)"
      ]
    )
  , ( [d| type role Labelled nominal representational
          newtype Labelled l a = UnsafeLabelled a
      |]
    , [ "newtype Labelled a b = UnsafeLabelled b"
      , "type role Labelled nominal representational"
      ]
    )
  , ( [d| newtype Fix f = In { out :: f (Fix f) }
          deriving
            instance (forall a. Show_ a => Show_ (f a)) => Show_ (Fix f)
      |]
    , [ "newtype Fix a = In { out :: (a (Fix a)) }"
      , "deriving"
      , "  instance (forall b. Main.Show_ b => Main.Show_ (a b))"
      , "        => Main.Show_ (Fix a)"
      ]
    )
  , ( [d| class Foo s where
            foo :: s -> String_
            default foo :: Show_ s => s -> String_
            foo = show_
      |]
    , [ "class Foo a where"
      , "  {         foo =  Main.show_"
      , "  ;         foo ::                 a -> Main.String_"
      , "  ; default foo :: Main.Show_ a => a -> Main.String_"
      , "  }"
      ]
    )
  , ( [d| pattern J x = Just_ x
      |]
    , [ "pattern J a = Main.Just_ a"
      ]
    )
  , ( [d| pattern Even :: Integral_ i => i
          pattern Even <- (even_ -> True_)
            where Even = 0
      |]
    , [ "pattern Even <- (Main.even_ -> Main.True_)"
      , "  where Even = 0"
      , "pattern Even :: forall a. Main.Integral_ a => a"
      ]
    )
  , ( [d| data Some f where Some :: f x -> Some f
          pattern SomeMore :: f x -> y -> (Some f, y)
          pattern SomeMore fx y = (Some fx, y)
      |]
    , [ "data Some a where Some :: forall a b. (a b) -> Some a"
      , "pattern SomeMore a b = (Some a, b)"
      , "pattern SomeMore :: forall a b. ()"
      , "                 => forall c. a c -> b -> (Some a, b)"
      ]
    )
  ]

-- }}}

-- --< expressions >-- {{{

data Test a b = Foo{ field1 :: a, field2 :: b }

otherwise_ :: Bool_
otherwise_ = True_

(*~) :: Num a => a -> a -> a
(*~) = (*)
infixl 7 *~

const_ :: x -> y -> x
const_ x y = x

expressions :: IO (Sum Int, Sum Int)
expressions = foldMap (uncurry test)
  [ ( [e| x |]
    , ["x"]
    )
  , ( [e| otherwise_ |]
    , ["Main.otherwise_"]
    )
  , ( [e| True_ |]
    , ["Main.True_"]
    )
  , ( [e| Just_ x |]
    , ["Main.Just_ x"]
    )
  , ( [e| ('a', "bcd", 0, 1.25, 2#, 3##, 4.75#, 5.5##, "prim"#, 'p'#) |]
    , ["('a', \"bcd\", 0, 1.25, 2#, 3##, 4.75#, 5.5##, \"prim\"#, 'p'#)"]
    )
  , ( [e| f x |]
    , ["f x"]
    )
  , ( [e| show_ @Bool_ |]
    , ["Main.show_ @Main.Bool_"]
    )
  , ( [e| x +~ y *~ z |]
    , ["(Main.+~) x ((Main.*~) y z)"]
    )
  , ( [e| (x) |]
    , ["x"]
    )
  , ( [e| \x k -> k x |]
    , ["\\a b -> b a"]
    )
  , ( [e| \x -> \x -> x |]
    , ["\\a -> \\b -> b"]
    )
  , ( [e| \(x :: y) -> x :: y |]
    , ["\\(a :: b) -> a :: b"]
    )
  , ( [e| \(x :: x) -> x :: x |]
    , ["\\(a :: b) -> a :: b"]
    )
  , ( [e| \case { x -> x } |]
    , ["\\case { a -> a }"]
    )
  , ( [e| (f, x, f x) |]
    , ["(f, x, f x)"]
    )
  , ( [e| (# f, x, f x #) |]
    , ["(# f, x, f x #)"]
    )
  , ( [e| (# | x | #) |]
    , ["(# | x | #)"]
    )
  , ( [e| if b then x else y |]
    , ["if b then x else y"]
    )
  , ( [e| if | b1 -> x | b2 -> y | b3 -> z |]
    , ["if | b1 -> x | b2 -> y | b3 -> z"]
    )
  , ( [e| let y x = f (x x) in y y |]
    , ["let a b = f (b b) in a a"]
    )
  , ( [e| case x of y -> y y |]
    , ["case x of { a -> a a }"]
    )
  , ( [e| do y <- foo x
             z <- foo y
             bar y z
      |]
    , [ "do { a <- foo x"
      , "   ; b <- foo a"
      , "   ; bar a b"
      , "   }"
      ]
    )
  , ( [e| [bar y z | y <- foo x, z <- foo y] |]
    , ["[bar a b | a <- foo x, b <- foo a]"]
    )
  , ( [e| [0, 1.. 9] |]
    , ["[0, 1.. 9]"]
    )
  , ( [e| [0, 1, 2, 3] |]
    , ["[0, 1, 2, 3]"]
    )
  , ( [e| const_ :: x -> y -> x |]
    , ["Main.const_ :: x -> y -> x"]
    )
  , ( [e| Foo{ field1 = 0, field2 = 'a' } |]
    , ["Main.Foo{ Main.field1 = 0, Main.field2 = 'a' }"]
    )
  , ( [e| foo{ field2 = 'b' } |]
    , ["foo{ Main.field2 = 'b' }"]
    )
  , ( [e| #label |]
    , ["#label"]
    )
  , ( [e| ?param |]
    , ["?param"]
    )
  , ( [e| foo.field1 |]
    , ["foo.field1"]
    )
  , ( [e| (.field1.field2) |]
    , ["(.field1.field2)"]
    )
  ]

-- }}}

-- --< patterns >-- {{{

data Test2 a b = a :* b

patterns :: IO (Sum Int, Sum Int)
patterns = foldMap (uncurry test)
  [ ( [p| 5 |]
    , ["5"]
    )
  , ( [p| x |]
    , ["x"]
    )
  , ( [p| (x, y, z) |]
    , ["(x, y, z)"]
    )
  , ( [p| (# x, y, z #) |]
    , ["(# x, y, z #)"]
    )
  , ( [p| (# x | #) |]
    , ["(# x | #)"]
    )
  , ( [p| Foo @a @b x y |]
    , ["Main.Foo @a @b x y"]
    )
  , ( [p| Just_ x :* _ |]
    , ["(Main.:*) (Main.Just_ x) _"]
    )
  , ( [p| ((Just_ x) :* _) |]
    , ["(Main.:*) (Main.Just_ x) _"]
    )
  , ( [p| ~((Just_ x) :* _) |]
    , ["~((Main.:*) (Main.Just_ x) _)"]
    )
  , ( [p| !((Just_ x) :* _) |]
    , ["!((Main.:*) (Main.Just_ x) _)"]
    )
  , ( [p| y@((Just_ x) :* _) |]
    , ["y@((Main.:*) (Main.Just_ x) _)"]
    )
  , ( [p| _ |]
    , ["_"]
    )
  , ( [p| Foo { field1 = x, field2 = y } |]
    , ["(Main.Foo { Main.field1 = x, Main.field2 = y })"]
    )
  , ( [p| Foo {field1,field2} |]
    , ["(Main.Foo { Main.field1 = field1, Main.field2 = field2 })"]
    )
  , ( [p| [_, x, Just_ y] |]
    , ["[_, x, Main.Just_ y]"]
    )
  , ( [p| Foo (x :: a) (y :: b) |]
    , ["Main.Foo (x :: a) (y :: b)"]
    )
  , ( [p| (even_ -> True_) |]
    , ["(Main.even_ -> Main.True_)"]
    )
  ]

-- }}}

-- --< types >-- {{{

data Proxy_ p

types :: IO (Sum Int, Sum Int)
types = foldMap (uncurry test)
  [ ( [t| forall x y. x -> y -> Test x y |]
    , ["forall a b. a -> b -> Main.Test a b"]
    )
  , ( [t| forall x -> forall y -> x -> y -> Test x y |]
    , ["forall a -> forall b -> a -> b -> Main.Test a b"]
    )
  , ( [t| forall k (x :: k). Proxy_ @k (x :: k) |]
    , ["forall a (b :: a). Main.Proxy_ @a (b :: a)"]
    )
  , ( [t| forall k (x :: k). Proxy_ @k (x :: k) |]
    , ["forall a (b :: a). Main.Proxy_ @a (b :: a)"]
    )
  , ( [t| forall k1 k2 (x :: k1) (y :: k2). 'Foo @k1 @k2 x y |]
    , ["forall a b (c :: a) (d :: b). 'Main.Foo @a @b c d"]
    )
  , ( [t| forall x y. x ':* y |]
    , ["forall a b. '(Main.:*) a b"]
    )
  , ( [t| (forall x y. (x ':* y)) |]
    , ["forall a b. '(Main.:*) a b"]
    )
  , ( [t| forall x y. (x, y, Test x y) |]
    , ["forall a b. (a, b, Main.Test a b)"]
    )
  , ( [t| forall x y. (# x, y, Test x y #) |]
    , ["forall a b. (# ,, #) a b (Main.Test a b)"]
    )
  , ( [t| forall c s. c s => forall t -> s ~ t => Bool_ |]
    , ["forall a b. a b => forall c -> b ~ c => Main.Bool_"]
    )
  , ( [t| forall x y. (x -> y) -> [x] -> [y] |]
    , ["forall a b. (a -> b) -> [a] -> [b]"]
    )
  , ( [t| forall x. (?foo :: x) => x -> x  |]
    , ["forall a. (?foo :: a) => a -> a"]
    )
  ]

-- }}}

-- --< test >-- {{{

test
  :: (Canonical a, Ppr a, Show a)
  => IO a -> [String] -> IO (Sum Int, Sum Int)
test q ls = do
  let s = unlines ls
  ast <- canonical <$> q
  let s' = respace (pprint ast)
  if ((==) `on` words) s s'
    then pure (1, 1)
    else do
      putStrLn "\nTest failed!\n\nExpected:"
      putStrLn s
      putStrLn "But generated:"
      putStrLn s'
      putStrLn "I.e.:"
      print ast $> (0, 1)
 where
  respace :: String -> String
  respace = slide sep
   where
    sep '{'  r  | r /= ' '                   = "{ " ++ [r]
    sep  l  '}' | l /= ' '                   = l:" }"
    sep ' ' '.'                              = "."
    sep  l  ';' | l /= ' '                   = l:" ;"
    sep '|'  r  | r /= ' ', not (isSymbol r) = "| " ++ [r]
    sep  l  '|' | l /= ' ', not (isSymbol l) = l:" |"
    sep  l   r                               = [l,r]

    slide :: (a -> a -> [a]) -> [a] -> [a]
    slide f (x:y:zs) = case f x y of
      [   ] ->    slide f        zs
      x':ys -> x':slide f (ys <> zs)
    slide _      zs  = zs

-- }}}

-- --< main >-- {{{

main :: IO ()
main = do
  (Sum passed, Sum total) <- declarations <> expressions <> patterns <> types
  putStrLn $ "\n" <> show passed  <> "/" <> show total <> " tests passed."
  if passed == total
    then exitSuccess
    else exitFailure

-- }}}

