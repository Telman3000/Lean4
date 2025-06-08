namespace Learn

open Nat

-- Ex 6: сначала определяем Sign и сам тип Int.mkInt
def subNat : Nat → Nat → Nat
  | n,     zero   => n
  | zero,  succ _ => zero
  | succ n, succ m => subNat n m


def addInt : Int → Int → Int
  | Int.pos n, Int.pos m =>
    Int.pos (n + m)

  | Int.neg n, Int.neg m =>
    -- −(n+1) + −(m+1) = −(n+m+2) = neg (n+m+1)
    Int.neg (n + m + 1)

  | Int.pos n, Int.neg m =>
    let k := m + 1
    if k ≤? n then
      -- +(n) + (−k) = +(n−k)
      Int.pos (subNat n k)
    else
      -- +(n) + (−k) = −(k−n) = neg (k−n−1)
      Int.neg (subNat k n - 1)

  | Int.neg n, Int.pos m =>
    -- коммутативность
    addInt (Int.pos m) (Int.neg n)
end Learn
