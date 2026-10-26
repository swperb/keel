# Bend's demos/pure_par_sum, scaled from d = 16 to d = 30. The demo's Nat
# sum overflows Bend's 2^48 Nat limit past d = 24, so the sum is a U32 here
# (the sum mod 2^32, which the Keel and Rust versions also print).
# Expected output: 3758096384.
import Base

def sum(d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      i
    case 1n++p:
      a b = sum(p, i) sum(p, U32.add(U32.shln(1, p), i))
      U32.add(a, b)

def main() -> IO(Unit):
  IO.print(U32.show(sum!(30n, 0)))
