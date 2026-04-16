import Informal

open Informal

namespace Test.Signature.Defs

@[informal "Definition 1.1" complete]
def foo (n : Nat) : Nat := n + 1

@[informal "Theorem 2.1" "forward only"]
theorem bar : 1 = 1 := rfl

def untagged : Bool := true

end Test.Signature.Defs
