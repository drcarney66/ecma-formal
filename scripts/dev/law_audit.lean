import Engine.Model
open Engine Engine.Model Ecma

def sh (x : MathVal) : String := toString x.toQ
def same (a b : MathVal) : Bool := sh a == sh b
def xs : List MathVal := [.int 0, .int 1, .int (-3), .int 7, .ofQ (1/3), .ofQ (-5/7), .ofQ (1/2), .ofQ (-3/4),
  Impl.sqrt (.int 2), Impl.pi, Impl.fn .exp (.int 1), Impl.pow (.int 2) (.ofQ (1/3)), Impl.pow (.int 2) (.int 2000), Impl.pow (.int 10) (.int 400)]
def check (name : String) (bad : List String) : IO Unit :=
  IO.println s!"{if bad.isEmpty then "ok  " else "FAIL"} {name}{if bad.isEmpty then "" else "  e.g. " ++ bad.head! ++ s!"  ({bad.length} of the samples)"}"
def tri := xs.flatMap fun a => xs.flatMap fun b => xs.map fun c => (a, b, c)
def duo := xs.flatMap fun a => xs.map fun b => (a, b)
def zero : MathVal := Impl.ofNat 0
def one : MathVal := Impl.ofNat 1
#eval do
  check "add_assoc" (tri.filterMap fun (a, b, c) => if same (Impl.add (Impl.add a b) c) (Impl.add a (Impl.add b c)) then none else some s!"{sh a}, {sh b}, {sh c}")
  check "add_comm" (duo.filterMap fun (a, b) => if same (Impl.add a b) (Impl.add b a) then none else some s!"{sh a}, {sh b}")
  check "add_zero" (xs.filterMap fun a => if same (Impl.add a zero) a then none else some (sh a))
  check "add_neg" (xs.filterMap fun a => if same (Impl.add a (Impl.neg a)) zero then none else some (sh a))
  check "sub_def" (duo.filterMap fun (a, b) => if same (Impl.sub a b) (Impl.add a (Impl.neg b)) then none else some s!"{sh a}, {sh b}")
  check "mul_assoc" (tri.filterMap fun (a, b, c) => if same (Impl.mul (Impl.mul a b) c) (Impl.mul a (Impl.mul b c)) then none else some s!"{sh a}, {sh b}, {sh c}")
  check "mul_comm" (duo.filterMap fun (a, b) => if same (Impl.mul a b) (Impl.mul b a) then none else some s!"{sh a}, {sh b}")
  check "mul_one" (xs.filterMap fun a => if same (Impl.mul a one) a then none else some (sh a))
  check "mul_add" (tri.filterMap fun (a, b, c) => if same (Impl.mul a (Impl.add b c)) (Impl.add (Impl.mul a b) (Impl.mul a c)) then none else some s!"{sh a}, {sh b}, {sh c}")
  check "div_mul" (duo.filterMap fun (a, b) => if same b zero || same (Impl.mul (Impl.div a b) b) a then none else some s!"{sh a}, {sh b}")
  check "lt_irrefl" (xs.filterMap fun a => if Impl.lt a a == false then none else some (sh a))
  check "lt_trans" (tri.filterMap fun (a, b, c) => if !(Impl.lt a b && Impl.lt b c) || Impl.lt a c then none else some s!"{sh a}, {sh b}, {sh c}")
  check "lt_total" (duo.filterMap fun (a, b) => if Impl.lt a b || same a b || Impl.lt b a then none else some s!"{sh a}, {sh b}")
  check "add_lt_add" (tri.filterMap fun (a, b, c) => if !Impl.lt a b || Impl.lt (Impl.add a c) (Impl.add b c) then none else some s!"{sh a}, {sh b}, {sh c}")
  check "mul_pos" (duo.filterMap fun (a, b) => if !(Impl.lt zero a && Impl.lt zero b) || Impl.lt zero (Impl.mul a b) then none else some s!"{sh a}, {sh b}")
  check "eq_iff" (duo.filterMap fun (a, b) => if Impl.eq a b == same a b then none else some s!"{sh a}, {sh b}")
  check "pow_zero" (xs.filterMap fun a => if same (Impl.pow a zero) one then none else some (sh a))
  check "pow_succ(3)" (xs.filterMap fun a => if same (Impl.pow a (Impl.ofNat 3)) (Impl.mul (Impl.pow a (Impl.ofNat 2)) a) then none else some (sh a))
  check "floor_isInt" (xs.filterMap fun a => if Impl.isInt (Impl.floor a) then none else some (sh a))
  check "floor_le" (xs.filterMap fun a => if Impl.lt a (Impl.floor a) == false then none else some (sh a))
  check "lt_floor_add_one" (xs.filterMap fun a => if Impl.lt a (Impl.add (Impl.floor a) one) then none else some (sh a))
  check "bigVal_bigOf" (xs.filterMap fun a => if !Impl.isInt a || same (Impl.bigVal (Impl.bigOf a)) a then none else some (sh a))
  check "bigVal_isInt" (xs.filterMap fun a => if Impl.isInt (Impl.bigVal (Impl.bigOf a)) then none else some (sh a))
  let n1 : BitVec 64 := 0x7ff8000000000000
  let n2 : BitVec 64 := 0x7ff8000000000001
  IO.println s!"numView_inj at two NaN patterns: views equal {match Impl.numView n1, Impl.numView n2 with | .nan, .nan => true | _, _ => false}, values equal {n1 == n2}"
