namespace Learn

-- Открываем пространство имен чтобы не писать лишние Nat._ _ _
open Nat

--Ex 1.1

-- берём два натурала числа и возвращаем также натурала
def multNat : Nat → Nat → Nat
-- | это обозначает начало новой "строки уравнений"
-- первый аргумент = 0, второй аргумент игнорируем
  | zero, _ => zero  -- 0*m=0
  -- succ k -> натуральное число k+1
  | succ k, m => m + multNat k m -- k+1)*m = m + k * m
#eval multNat 5 2 /- подстовляем
и происходит
multNat 5 2
= 2 + (2 + (2 + (2 + (2 + 0))))
= 2 + (2 + (2 + (2 + 2)))
= 2 + (2 + (2 + 4))
= 2 + (2 + 6)
= 2 + 8
= 10

так как
5 = succ (succ (succ (succ (succ zero))))
берем каждый раз с "хвоста"
-/

-- Ex 1.2


def expNat : Nat → Nat → Nat
  | _,     zero   => succ zero            -- n^0 = 1
  | n,     succ k => multNat n (expNat n k)
/- когда показатель имеет вид succ k (т. е. равен k+1),
сначала рекурсивно вычисляем expNat n k (то есть n^k),
а затем умножаем результат на n через multNat.

expNat 2 3
Поскольку 3 = succ 2 ==>
expNat 2 3 = multNat 2 (expNat 2 2) ==>
expNat 2 2 = multNat 2 (expNat 2 1)
... == > expNat 2 0 = succ zero = 1

После все подставляется в обратном порядке
expNat 2 1 = multNat 2 1   ->  = 2 * 1 = 2
expNat 2 2 = multNat 2     ->  = 2 * 2 = 4
expNat 2 3 = multNat 2 4   ->  = 2 * 4 = 8

-/
#eval expNat 2 3 -- = 8
--#eval expNat 5 2  -- = 25



-- Ex 2.1 Строгое неравенство <

inductive LessThanNat : Nat → Nat → Type where
  | zeroEq (m : Nat) : LessThanNat zero (succ m)
    -- 0 < (m+1) для любого m
  | lt_succ {m n : Nat} (h : LessThanNat m n) :
      LessThanNat (succ m) (succ n)
    -- из m < n следует (m+1) < (n+1)
/-
1 - zero < succ m задаёт все случаи 0 < k для k≥1.

2 - Затем «поднимаем» неравенство на единицу с помощью lt_succ.
и так далее
-/


--Ex 2.2 Нестрогое неравенство ≤

/--/ inductive -- объявляет новый индуктивный (рекурсивно определяемый) тип
: Nat → Nat → Type -->
--> для любых двух Nat это выдаёт логическое утверждение -/
inductive LessOrEqNat : Nat → Nat → Type where
  | zeroEq (n : Nat) : LessOrEqNat zero n
    -- 0 ≤ n для любого n
  | le_succ {m n : Nat} (h : LessOrEqNat m n) :
      LessOrEqNat (succ m) (succ n)
    -- из m ≤ n следует (m+1) ≤ (n+1)



-- Ex 3
--подход 2 чтобы не было коллизии +0 и −0
inductive Int : Type where
 -- pos конутсруктор добавления + к числу
 -- neg наоборот - к числу
  | pos : Nat → Int  -- +n
  | neg : Nat → Int  -- −(n+1)

-- Два целых равны тогда и только тогда,
-- когда совпадают конструкторы и аргументы:
inductive IntEq : Int → Int → Type where
  | eq_pos (n : Nat) : IntEq (Int.pos n) (Int.pos n)
  | eq_neg (n : Nat) : IntEq (Int.neg n) (Int.neg n)
 -- для любого n есть eq_pos n : IntEq (pos n) (pos n).




--Ex 4.1
-- Открываем пространство имен чтобы не писать лишние Int.pos/neg
namespace Int

-- +1 к целому
def incrementInt : Int → Int
  | pos n      => pos (succ n)           -- +n +1 = +(n+1)
  | neg zero   => pos zero               -- −1 +1 = 0
  | neg (succ n) => neg n                -- −(n+2)+1 = −(n+1)

--Ex 4.2
-- −1 от целого
def decrementInt : Int → Int
  | pos zero    => neg zero              -- 0 −1 = −1
  | pos (succ n) => pos n                -- +(n+1)−1 = +n
  | neg n       => neg (succ n)          -- −(n+1)−1 = −(n+2)

--Ex 4.3
-- Проверяет, равно ли число нулю.
def isZeroInt : Int → Bool
  | pos zero => true
  | _        => false



--Ex 5

def inject (n : Nat) : Int :=
  pos n  --  т.е. Int.pos n от inductive Int
#eval inject 3  -- выдаст `pos 3`, т.е.  +3


--Ex 6




-- Ex 7

def multNat : Nat → Nat → Nat
  | zero   , _ => zero
  | succ k , m => m + multNat k m

#eval multNat 3 3   -- 9
#eval multNat 32 2  -- 64




-- Ex 8
structure Rational where
  num : Int   -- числитель
  den : Nat   -- хранит d так, что реально знаменатель = d+1


--Ex 9
def RationalEq (a b : Rational) : Prop :=
  IntEq
    (multInt a.num (inject (b.den + 1)))
    (multInt b.num (inject (a.den + 1)))
