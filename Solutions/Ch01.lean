/-! Solutions — Chapter 1. Peek only after a real attempt. -/
namespace Sol01

def double (n : Nat) : Nat := 2 * n
#guard double 0 == 0
#guard double 21 == 42

def max3 (a b c : Nat) : Nat := max a (max b c)
#guard max3 1 2 3 == 3
#guard max3 9 2 3 == 9
#guard max3 1 9 3 == 9
#guard max3 4 4 4 == 4

def isEven (n : Nat) : Bool := n % 2 == 0
#guard isEven 0 == true
#guard isEven 7 == false
#guard isEven 12 == true

def greet (name : String) : String := "Hello, " ++ name ++ "!"
#guard greet "Ada" == "Hello, Ada!"
#guard greet "Lean" == "Hello, Lean!"

def fizzbuzz (n : Nat) : String :=
  if n % 15 == 0 then "FizzBuzz"
  else if n % 3 == 0 then "Fizz"
  else if n % 5 == 0 then "Buzz"
  else toString n
#guard fizzbuzz 1 == "1"
#guard fizzbuzz 3 == "Fizz"
#guard fizzbuzz 5 == "Buzz"
#guard fizzbuzz 15 == "FizzBuzz"
#guard fizzbuzz 7 == "7"

def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#guard applyTwice (· + 3) 10 == 16
#guard applyTwice (· * 2) 5 == 20

end Sol01
