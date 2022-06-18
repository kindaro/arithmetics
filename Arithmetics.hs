module Arithmetics where

import Prelude qualified
import Data.Functor.Foldable
import Data.Fix
import Data.Vector.Sized
import GHC.TypeNats
import Prelude (Bool(..), Foldable (..), Num (..), Show (..), Semigroup (..), error, Functor, Int, Eq, otherwise, Maybe (..))
import Data.Functor.Classes
import Generic.Data
import Prelude.Unicode
import Data.String
import Data.Text (Text)
import Data.Type.Equality
import Data.Function
import Type.Reflection
import Data.Proxy

(▵) ∷ (input → left) → (input → right) → input → (left, right)
function ▵ gunction = \ input → (function input, gunction input)
infixr 7 ▵

pattern E ∷ Vector 0 value
pattern E ← (null → True) where E = empty

pattern (:>) ∷ value → Vector length value → Vector (1 + length) value
pattern value :> values ← (head ▵ tail → (value, values)) where value :> values = value `cons` values
infixr 5 :>

pattern (:∎) ∷ value → value → Vector 2 value
pattern one :∎ other ← (head ▵ last → (one, other)) where one :∎ other = one :> singleton other
infixr 5 :∎

data Wender constant variable recursion where
  Constant ∷ constant → Wender constant variable recursion
  Variable ∷ variable → Wender constant variable recursion
  Operator ∷ KnownNat arity ⇒ Operator arity → Vector arity recursion → Wender constant variable recursion

deriving instance Functor (Wender constant variable)

data Operator arity where
  Add ∷ Operator 2
  Multiply ∷ Operator 2
  Negate ∷ Operator 1
  Invert ∷ Operator 1

deriving instance Eq (Operator arity)

type Expression constant variable = Fix (Wender constant variable)

type family Unfix value = result | result → value where Unfix (Fix value) = value (Fix value)

pattern (:×) ∷ Expression constant variable → Expression constant variable → Expression constant variable
pattern one :× other = Fix (Operator Multiply (one :∎ other))

pattern (:+) ∷ Expression constant variable → Expression constant variable → Expression constant variable
pattern one :+ other = Fix (Operator Add (one :∎ other))

parenthesize ∷ (Semigroup text, IsString text) ⇒ text → text
parenthesize text = "(" <> text <> ")"

instance {-# overlapping #-} (Show constant, Show variable) ⇒ Show (Expression constant variable) where
  show (one :+ other) = parenthesize do show one <> " + " <> show other
  show (one :× other) = parenthesize do show one <> " × " <> show other
  show (Fix (Constant constant)) = show constant
  show (Fix (Variable variable)) = show variable
  show _ = error "not implemented"

instance Num constant ⇒ Num (Expression constant variable) where
  one + other = one :+ other
  one * other = one :× other
  fromInteger = Fix ∘ Constant ∘ fromInteger
  negate = Fix ∘ Operator Negate ∘ singleton

instance {-# overlapping #-} (Eq constant, Eq variable) ⇒ Eq (Expression constant variable) where
  Fix one == Fix other = one ≡ other

equate ∷ (Typeable α, Typeable β) ⇒ α → β → Maybe (α :~: β)
equate α β = testEquality (typeOf α) (typeOf β)

proxify ∷ f α → Proxy α
proxify _ = Proxy

operate ∷ Num number ⇒ Operator 2 → number → number → number
operate Add x y = x + y
operate Multiply x y = x × y

instance (Eq constant, Eq variable, Eq recursion) ⇒ Eq (Wender constant variable recursion) where
  Constant one == Constant other = one ≡ other
  Variable one == Variable other = one ≡ other
  Operator operator vector == Operator surgeon point = case equate operator surgeon of
    Just Refl → vector ≡ point
    Nothing → False
  _ == _ = False

instance IsString (Expression constant Text) where
  fromString = Fix ∘ Variable ∘ fromString

normalize ∷ Num number ⇒ Unfix (Expression number variable) → Expression number variable
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( Fix (Constant one) :∎ Fix
      ( Operator surgeon@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
        ( ( Fix (Constant other) ) :∎ remainder ) ) ) )
  | operator ≡ surgeon = Fix (Operator operator (Fix (Operator operator (Fix (Constant one) :∎ Fix (Constant other))) :∎ remainder))
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( Fix (Constant one) :∎ Fix (Constant other) ) ) = Fix (Constant (operate operator one other))
normalize expression = case Fix expression of
  multiple@(Fix (Constant _)) :× (salmon :+ trout)
    → (multiple :× salmon) :+ (multiple :× trout)
  (subexpression :+ constant@(Fix (Constant _))) → constant :+ subexpression
  _ → Fix expression

converge :: Eq a => [a] -> [a]
converge = convergeBy (≡)

fixate :: Eq a => (a -> a) -> a -> a
fixate f = Prelude.last ∘ converge ∘ Prelude.iterate f

convergeBy :: (a -> a -> Bool) -> [a] -> [a]
convergeBy _ [ ] = [ ]
convergeBy _ [x] = [x]
convergeBy eq (x: xs@(y: _))
    | x `eq` y = [x]
    | otherwise = x: convergeBy eq xs
