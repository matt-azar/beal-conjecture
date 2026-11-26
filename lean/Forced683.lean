import QuadraticBridge

/-! For each remaining twist at d=2471, reduction at the two places over
683 forces the right base to vanish in F₆₈₃. The cyclic calculation below
covers arbitrary exponent lifts, including exponent representatives 5 and 67. -/
namespace Beal.Forced683
open QuadraticBridge

def place : Twist2471.Place := ⟨683, 332, 22⟩

def passes (a k b : Nat) : Bool :=
  let test := fun s =>
    Twist2471.powerTest place ((Twist2471.eta 683 s ^ k * (b^2 + a*s)) % 683)
  test 332 && test 351

def candidates (a k : Nat) := (List.range 683).filter (passes a k)

set_option exponentiation.threshold 1600
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem at5 : candidates (2471^2 % 683) 23 = [26, 657] := by decide
theorem at67 : candidates (2471^33 % 683) 8 = [298, 385] := by decide

private theorem period (n e j : Nat) (cycle : 2471^(n*11) % 683 = 1) :
    2471^(e+n*j) % 683 = 2471^(e+n*(j%11)) % 683 := by
  have expand : e+n*j = e+n*(j%11)+(n*11)*(j/11) := by
    rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add]
    rw [Nat.mod_add_div j 11]
  rw [expand, Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [pow_mod_congr (b := 1) (m := 683) cycle, Nat.one_pow]
  simp

/-- Each row tests the norm residue for all b that pass both twist embeddings. -/
def normTest (r e k : Nat) : Bool := (List.range 11).all fun j =>
  let a := 2471^(e+62*j) % 683
  let n := 2471^(r+124*j) % 683
  (candidates a k).all fun b => (n+b^4) % 683 == 0

theorem norm5 : normTest 5 2 23 = true := by decide
theorem norm67 : normTest 67 33 8 = true := by decide

private theorem accepts (y : Nat) (hy : y < 683) :
    Twist2471.powerTest place (y^31 % 683) = true := by
  have t := List.all_eq_true.mp Twist2471.powerTest_sound place (by decide)
  exact List.all_eq_true.mp t y (List.mem_range.mpr hy)

private theorem prod_mod (q a a' s b : Nat) (ha : a % 683 = a' % 683) :
    q*(b^2+a*s) % 683 = q*(b^2+a'*s) % 683 := by
  have hu : (a*s)%683=(a'*s)%683 := by rw [Nat.mul_mod, ha, ← Nat.mul_mod]
  have hv : (b^2+a*s)%683=(b^2+a'*s)%683 := by rw [Nat.add_mod, hu, ← Nat.add_mod]
  rw [Nat.mul_mod, hv, ← Nat.mul_mod]

private theorem divisor_of_twist (r e k b c j : Nat) (beta : Element)
    (hTable : normTest r e k = true)
    (identity : pow 618 beta 31 = mul 618 (pow 618 eta2471 k)
      (gamma (2471^(e+62*j)) b))
    (eqn : 2471^(r+124*j)+b^4=c^31) : 683 ∣ c := by
  let a := 2471^(e+62*(j%11)) % 683
  let br := residue 683 b
  have br_eq : br = b % 683 := by
    dsimp [br, residue]
    rfl
  have ha : 2471^(e+62*j) % 683 = a % 683 := by
    dsimp [a]
    rw [Nat.mod_mod]
    exact period 62 e j (by decide)
  have passesAt (s : Nat)
      (hs : Reduction 618 eta2471 683 s (Twist2471.eta 683 s) (omegaResidue 683 s)) :
      Twist2471.powerTest place ((Twist2471.eta 683 s ^ k * (br^2+a*s)) % 683) = true := by
    obtain ⟨y,hy,he⟩ := reduce_twist hs identity
    rw [← prod_mod _ (2471^(e+62*j)) a s br ha, ← he]
    exact accepts y hy
  have ok : br ∈ candidates a k := List.mem_filter.mpr ⟨List.mem_range.mpr (by rw [br_eq]; exact Nat.mod_lt _ (by decide)),
    Bool.and_eq_true_iff.mpr ⟨passesAt 332 (by decide), passesAt 351 (by decide)⟩⟩
  have hj : j % 11 ∈ List.range 11 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have hnorm := of_decide_eq_true (show decide
      ((2471^(r+124*(j%11))%683+br^4)%683 = 0) = true from
      by simpa using List.all_eq_true.mp (List.all_eq_true.mp hTable _ hj) _ ok)
  have hc : c^31 % 683 = 0 := by
    rw [← eqn, Nat.add_mod, period 124 r j (by decide),
        pow_mod_congr (Nat.mod_mod b 683).symm 4, ← br_eq]
    rw [Nat.add_mod, Nat.mod_mod] at hnorm
    exact hnorm
  have onlyZero : (List.range 683).all (fun z => z^31 % 683 != 0 || z == 0) = true := by decide
  have z := List.all_eq_true.mp onlyZero (c%683) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rw [pow_mod_congr (Nat.mod_mod c 683).symm 31] at hc
  simp [hc] at z
  exact Nat.dvd_of_mod_eq_zero z

/-- Conditional on the shared twist delivered by the ideal-class descent, 683
divides c in each of the two surviving exponent classes, for every j. -/
theorem forced683_at5 (b c j : Nat) (beta : Element)
    (identity : pow 618 beta 31 = mul 618 (pow 618 eta2471 23)
      (gamma (2471^(2+62*j)) b))
    (eqn : 2471^(5+124*j)+b^4=c^31) : 683 ∣ c :=
  divisor_of_twist 5 2 23 b c j beta norm5 identity eqn

theorem forced683_at67 (b c j : Nat) (beta : Element)
    (identity : pow 618 beta 31 = mul 618 (pow 618 eta2471 8)
      (gamma (2471^(33+62*j)) b))
    (eqn : 2471^(67+124*j)+b^4=c^31) : 683 ∣ c :=
  divisor_of_twist 67 33 8 b c j beta norm67 identity eqn

end Beal.Forced683

#print axioms Beal.Forced683.forced683_at5
#print axioms Beal.Forced683.forced683_at67
