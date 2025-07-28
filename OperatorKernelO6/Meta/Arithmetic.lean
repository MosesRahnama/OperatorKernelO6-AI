import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

def num : Nat → Trace
| 0 => void
| n+1 => delta (num n)

@[simp] def toNat : Trace → Nat
| void => 0
| delta t => toNat t + 1
| integrate t => toNat t
| merge a b => toNat a + toNat b
| recΔ _ _ n => toNat n
| eqW _ _ => 0

@[simp] theorem toNat_num (n : Nat) : toNat (num n) = n := by
  induction n with
  | zero => simp [num, toNat]
  | succ n ih => simp [num, toNat, ih]

def add (a b : Trace) : Trace := num (toNat a + toNat b)
def mul (a b : Trace) : Trace := num (toNat a * toNat b)

@[simp] theorem toNat_add (a b : Trace) : toNat (add a b) = toNat a + toNat b := by
  simp [add, toNat_num]

@[simp] theorem toNat_mul (a b : Trace) : toNat (mul a b) = toNat a * toNat b := by
  simp [mul, toNat_num]

end OperatorKernelO6.Meta
