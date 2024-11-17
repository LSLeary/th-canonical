# *th-canonical*

This library provides a comparatively robust equivalence relation `~` on Template Haskell ASTs by transforming them to a `canonical` form before invoking `==`.
This lets you test your TH codegen against hand-written target code.

## Example

Testing a function `gensing`, which generates singleton `data instance`s from corresponding `type data` declarations.

```haskell
import Test.TH

tests :: [(String, Test)]
tests =
  [ ("foo ", $$foo )
  , ("list", $$list)
  ...
  ]

main = ...
```

```haskell
module Test.TH where

type Test = Equivalence (Rendered [Dec])

type data Foo = Bar | Quux

foo :: Code Q Test
foo = gensing ''Foo <~> [d|
    data instance Foo @ a where
      Bar  :: Foo @ Bar
      Quux :: Foo @ Quux
  |]

type data List a = Nil | Cons a (List a)

list :: Code Q Test
list = gensing ''List <~> [d|
    data instance List a @ b where
      Nil  ::                        List a @ Nil
      Cons :: a @ c -> List a @ d -> List a @ Cons c d
  |]

...
```
