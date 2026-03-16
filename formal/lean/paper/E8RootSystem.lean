/-
  E8RootSystem.lean — Complete E8 Root System (240 roots)

  All 240 roots explicitly enumerated and verified.
  112 Type D roots (±eᵢ±eⱼ) + 128 Type S roots ((±½)^8, even minus).
  Scaled by 2: Type D entries in {-2,0,2}, Type S entries in {-1,1}.

  Self-contained. No imports required.
  Compile: lean E8RootSystem.lean
-/

namespace E8RootSystem

abbrev V := Fin 8 → Int

def dot (a b : V) : Int :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 +
  a 4 * b 4 + a 5 * b 5 + a 6 * b 6 + a 7 * b 7

def norm2 (a : V) : Int := dot a a

def vadd (a b : V) : V := fun i => a i + b i

def isTypeD (v : V) : Bool :=
  norm2 v == 8 &&
  (v 0 == 0 || v 0 == 2 || v 0 == -2) && (v 1 == 0 || v 1 == 2 || v 1 == -2) &&
  (v 2 == 0 || v 2 == 2 || v 2 == -2) && (v 3 == 0 || v 3 == 2 || v 3 == -2) &&
  (v 4 == 0 || v 4 == 2 || v 4 == -2) && (v 5 == 0 || v 5 == 2 || v 5 == -2) &&
  (v 6 == 0 || v 6 == 2 || v 6 == -2) && (v 7 == 0 || v 7 == 2 || v 7 == -2)

def isTypeS (v : V) : Bool :=
  norm2 v == 8 &&
  (v 0 == 1 || v 0 == -1) && (v 1 == 1 || v 1 == -1) &&
  (v 2 == 1 || v 2 == -1) && (v 3 == 1 || v 3 == -1) &&
  (v 4 == 1 || v 4 == -1) && (v 5 == 1 || v 5 == -1) &&
  (v 6 == 1 || v 6 == -1) && (v 7 == 1 || v 7 == -1) &&
  (v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7) % 4 == 0

def isE8Root (v : V) : Bool := isTypeD v || isTypeS v

-- ================================================================
-- ALL 240 E8 ROOTS
-- ================================================================

private def r000 : V := fun i => if i == 0 then (2) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r001 : V := fun i => if i == 0 then (2) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r002 : V := fun i => if i == 0 then (-2) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r003 : V := fun i => if i == 0 then (-2) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r004 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r005 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r006 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r007 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r008 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r009 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r010 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r011 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r012 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r013 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r014 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r015 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r016 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r017 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r018 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r019 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r020 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r021 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r022 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r023 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r024 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r025 : V := fun i => if i == 0 then (2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r026 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r027 : V := fun i => if i == 0 then (-2) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r028 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r029 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r030 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r031 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r032 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r033 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r034 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r035 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r036 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r037 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r038 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r039 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r040 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r041 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r042 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r043 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r044 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r045 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r046 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r047 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r048 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r049 : V := fun i => if i == 0 then (0) else if i == 1 then (2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r050 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r051 : V := fun i => if i == 0 then (0) else if i == 1 then (-2) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r052 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r053 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r054 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r055 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r056 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r057 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r058 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r059 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r060 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r061 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r062 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r063 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r064 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r065 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r066 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r067 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r068 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r069 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r070 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r071 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (-2) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r072 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r073 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r074 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r075 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r076 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r077 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r078 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r079 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r080 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r081 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r082 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r083 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r084 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r085 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r086 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r087 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (-2) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r088 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r089 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r090 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r091 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (0) else 0
private def r092 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r093 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r094 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r095 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r096 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r097 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r098 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r099 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (-2) else if i == 5 then (0) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r100 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r101 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r102 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (2) else if i == 7 then (0) else 0
private def r103 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (-2) else if i == 7 then (0) else 0
private def r104 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r105 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (2) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r106 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (2) else 0
private def r107 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (-2) else if i == 6 then (0) else if i == 7 then (-2) else 0
private def r108 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (2) else 0
private def r109 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (2) else if i == 7 then (-2) else 0
private def r110 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (2) else 0
private def r111 : V := fun i => if i == 0 then (0) else if i == 1 then (0) else if i == 2 then (0) else if i == 3 then (0) else if i == 4 then (0) else if i == 5 then (0) else if i == 6 then (-2) else if i == 7 then (-2) else 0
private def r112 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r113 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r114 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r115 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r116 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r117 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r118 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r119 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r120 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r121 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r122 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r123 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r124 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r125 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r126 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r127 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r128 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r129 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r130 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r131 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r132 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r133 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r134 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r135 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r136 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r137 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r138 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r139 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r140 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r141 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r142 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r143 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (1) else 0
private def r144 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r145 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r146 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r147 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r148 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r149 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r150 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r151 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r152 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r153 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r154 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r155 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r156 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r157 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r158 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r159 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r160 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r161 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r162 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r163 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r164 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r165 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r166 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r167 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r168 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r169 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r170 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r171 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r172 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r173 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r174 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r175 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (1) else 0
private def r176 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r177 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r178 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r179 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r180 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r181 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r182 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r183 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r184 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r185 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r186 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r187 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r188 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r189 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r190 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r191 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r192 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r193 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r194 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r195 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r196 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r197 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r198 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r199 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r200 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r201 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r202 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r203 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r204 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r205 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r206 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r207 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (1) else if i == 7 then (-1) else 0
private def r208 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r209 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r210 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r211 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r212 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r213 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r214 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r215 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r216 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r217 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r218 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r219 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r220 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r221 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r222 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r223 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r224 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r225 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r226 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r227 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r228 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r229 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r230 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r231 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r232 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r233 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r234 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r235 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r236 : V := fun i => if i == 0 then (-1) else if i == 1 then (1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r237 : V := fun i => if i == 0 then (1) else if i == 1 then (-1) else if i == 2 then (1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r238 : V := fun i => if i == 0 then (1) else if i == 1 then (1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0
private def r239 : V := fun i => if i == 0 then (-1) else if i == 1 then (-1) else if i == 2 then (-1) else if i == 3 then (-1) else if i == 4 then (-1) else if i == 5 then (-1) else if i == 6 then (-1) else if i == 7 then (-1) else 0

def e8RootList : List V := [
  r000,
  r001,
  r002,
  r003,
  r004,
  r005,
  r006,
  r007,
  r008,
  r009,
  r010,
  r011,
  r012,
  r013,
  r014,
  r015,
  r016,
  r017,
  r018,
  r019,
  r020,
  r021,
  r022,
  r023,
  r024,
  r025,
  r026,
  r027,
  r028,
  r029,
  r030,
  r031,
  r032,
  r033,
  r034,
  r035,
  r036,
  r037,
  r038,
  r039,
  r040,
  r041,
  r042,
  r043,
  r044,
  r045,
  r046,
  r047,
  r048,
  r049,
  r050,
  r051,
  r052,
  r053,
  r054,
  r055,
  r056,
  r057,
  r058,
  r059,
  r060,
  r061,
  r062,
  r063,
  r064,
  r065,
  r066,
  r067,
  r068,
  r069,
  r070,
  r071,
  r072,
  r073,
  r074,
  r075,
  r076,
  r077,
  r078,
  r079,
  r080,
  r081,
  r082,
  r083,
  r084,
  r085,
  r086,
  r087,
  r088,
  r089,
  r090,
  r091,
  r092,
  r093,
  r094,
  r095,
  r096,
  r097,
  r098,
  r099,
  r100,
  r101,
  r102,
  r103,
  r104,
  r105,
  r106,
  r107,
  r108,
  r109,
  r110,
  r111,
  r112,
  r113,
  r114,
  r115,
  r116,
  r117,
  r118,
  r119,
  r120,
  r121,
  r122,
  r123,
  r124,
  r125,
  r126,
  r127,
  r128,
  r129,
  r130,
  r131,
  r132,
  r133,
  r134,
  r135,
  r136,
  r137,
  r138,
  r139,
  r140,
  r141,
  r142,
  r143,
  r144,
  r145,
  r146,
  r147,
  r148,
  r149,
  r150,
  r151,
  r152,
  r153,
  r154,
  r155,
  r156,
  r157,
  r158,
  r159,
  r160,
  r161,
  r162,
  r163,
  r164,
  r165,
  r166,
  r167,
  r168,
  r169,
  r170,
  r171,
  r172,
  r173,
  r174,
  r175,
  r176,
  r177,
  r178,
  r179,
  r180,
  r181,
  r182,
  r183,
  r184,
  r185,
  r186,
  r187,
  r188,
  r189,
  r190,
  r191,
  r192,
  r193,
  r194,
  r195,
  r196,
  r197,
  r198,
  r199,
  r200,
  r201,
  r202,
  r203,
  r204,
  r205,
  r206,
  r207,
  r208,
  r209,
  r210,
  r211,
  r212,
  r213,
  r214,
  r215,
  r216,
  r217,
  r218,
  r219,
  r220,
  r221,
  r222,
  r223,
  r224,
  r225,
  r226,
  r227,
  r228,
  r229,
  r230,
  r231,
  r232,
  r233,
  r234,
  r235,
  r236,
  r237,
  r238,
  r239
]

def inE8List (v : V) : Bool := e8RootList.any (fun w => 
  v 0 == w 0 && v 1 == w 1 && v 2 == w 2 && v 3 == w 3 &&
  v 4 == w 4 && v 5 == w 5 && v 6 == w 6 && v 7 == w 7)

-- ================================================================
-- VERIFIED PROPERTIES
-- ================================================================

/-- The E8 root system has exactly 240 roots. -/
theorem e8_root_count : e8RootList.length = 240 := by native_decide

/-- Every root in the list is a valid E8 root. -/
theorem e8_all_valid : e8RootList.all isE8Root = true := by native_decide

/-- Every root has norm² = 8 (= 2 in unscaled coordinates). -/
theorem e8_all_norm8 : e8RootList.all (fun v => norm2 v == 8) = true := by native_decide

/-- 112 roots are Type D. -/
theorem e8_typeD_count : (e8RootList.filter isTypeD).length = 112 := by native_decide

/-- 128 roots are Type S. -/
theorem e8_typeS_count : (e8RootList.filter isTypeS).length = 128 := by native_decide

/-- Count bracket-closing pairs using List.foldl. -/
def bracketPairCount : Nat :=
  let roots := e8RootList
  let pairs := roots.enum.foldl (fun acc (i, ri) =>
    acc + (roots.drop (i + 1)).countP (fun rj => isE8Root (vadd ri rj))
  ) 0
  pairs

/-- There are exactly 6720 bracket-closing pairs. -/
theorem e8_bracket_pairs : bracketPairCount = 6720 := by native_decide

end E8RootSystem