import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
Elementary lemmas from the arbitrary-square note at base 2471
(`docs/square-summand-2471.md`). These are the finite modular and
class-group calculations used in cases 2 and 4 of that note. They do
not depend on the Dedekind-domain development (L2b).
-/
namespace Beal.SquareSummand

/-! ## Modular helpers -/

def Cong (m : ℕ) (a b : ℤ) : Prop := a % (m : ℤ) = b % (m : ℤ)

theorem pow_mod_congr {a b m : ℕ} (h : a % m = b % m) (n : ℕ) :
    a ^ n % m = b ^ n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

private theorem add_cong {m : ℕ} {a b c d : ℤ} (h : Cong m a b) (g : Cong m c d) :
    Cong m (a + c) (b + d) := by
  unfold Cong at *
  rw [Int.add_emod a c, Int.add_emod b d, h, g]

private theorem mul_cong {m : ℕ} {a b c d : ℤ} (h : Cong m a b) (g : Cong m c d) :
    Cong m (a * c) (b * d) := by
  unfold Cong at *
  rw [Int.mul_emod a c, Int.mul_emod b d, h, g]

private theorem pow_cong {m : ℕ} {a b : ℤ} (h : Cong m a b) (n : ℕ) :
    Cong m (a ^ n) (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact mul_cong ih h

private theorem sub_cong {m : ℕ} {a b c d : ℤ} (h : Cong m a b) (g : Cong m c d) :
    Cong m (a - c) (b - d) := by
  unfold Cong at *
  rw [Int.sub_emod a c, Int.sub_emod b d, h, g]

/-- Lift a natural modular identity `a^n % m = r` to an integer congruence. -/
private theorem cong_of_nat_pow {a n m r : ℕ} (h : a ^ n % m = r) :
    Cong m ((a : ℤ) ^ n) r := by
  unfold Cong
  have hr : r % m = r := by rw [← h, Nat.mod_mod]
  calc ((a : ℤ) ^ n) % (m : ℤ)
      = ((a ^ n : ℕ) : ℤ) % (m : ℤ) := by rw [← Int.natCast_pow]
    _ = ((a ^ n % m : ℕ) : ℤ) := by rw [← Int.natCast_emod]
    _ = (r : ℤ) := by rw [h]
    _ = (r : ℤ) % (m : ℤ) := by rw [← Int.natCast_emod, hr]

/-! ## (i) Residues of `2471^x + U^2` -/

/-- Odd powers of `2471 ≡ 7 (mod 16)` remain `7` modulo 16. -/
theorem base_pow_odd_mod_sixteen {x : ℕ} (hx : x % 2 = 1) :
    (2471 : ℕ) ^ x % 16 = 7 := by
  have hd : (2471 : ℕ) % 16 = 7 := by decide
  have d2 : (2471 : ℕ) ^ 2 % 16 = 1 := pow_mod_congr (b := 7) (m := 16) hd 2
  have odd : x = 2 * (x / 2) + 1 := by omega
  conv => lhs; rw [odd, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod]
  rw [pow_mod_congr (b := 1) (m := 16) d2, Nat.one_pow, hd]

/-- Even integer squares are `0` or `4` modulo 16. -/
theorem even_sq_mod_sixteen {U : ℤ} (hU : U % 2 = 0) :
    Cong 16 (U ^ 2) 0 ∨ Cong 16 (U ^ 2) 4 := by
  have hmod : Cong 16 U 0 ∨ Cong 16 U 2 ∨ Cong 16 U 4 ∨ Cong 16 U 6 ∨
      Cong 16 U 8 ∨ Cong 16 U 10 ∨ Cong 16 U 12 ∨ Cong 16 U 14 := by
    unfold Cong
    have hlt : U % 16 < 16 := Int.emod_lt_of_pos U (by norm_num)
    have hnn : 0 ≤ U % 16 := Int.emod_nonneg U (by norm_num)
    have heven : (U % 16) % 2 = 0 := by
      have : U % 2 = (U % 16) % 2 := by
        rw [← Int.emod_emod_of_dvd U (by decide : (2 : ℤ) ∣ 16)]
      omega
    omega
  refine hmod.elim (fun h => Or.inl (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inr (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inl (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inr (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inl (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inr (by simpa using pow_cong h 2)) ?_
  intro h; refine h.elim (fun h => Or.inl (by simpa using pow_cong h 2)) ?_
  intro h; exact Or.inr (by simpa using pow_cong h 2)

/-- Case 4 of `docs/square-summand-2471.md`: with `x` odd and `U` even,
`2471^x + U^2 ≡ 7` or `11 (mod 16)`. -/
theorem sum_mod_sixteen_of_even_U {x : ℕ} {U : ℤ}
    (hx : x % 2 = 1) (hU : U % 2 = 0) :
    Cong 16 ((2471 : ℤ) ^ x + U ^ 2) 7 ∨
      Cong 16 ((2471 : ℤ) ^ x + U ^ 2) 11 := by
  have hd : Cong 16 ((2471 : ℤ) ^ x) 7 :=
    cong_of_nat_pow (base_pow_odd_mod_sixteen hx)
  rcases even_sq_mod_sixteen hU with hs | hs
  · left; simpa using add_cong hd hs
  · right; simpa using add_cong hd hs

/-- Case 2 of `docs/square-summand-2471.md`: with `U` odd,
`2471^x + U^2` is even. -/
theorem sum_even_of_odd_U {x : ℕ} {U : ℤ} (hU : U % 2 = 1) :
    Cong 2 ((2471 : ℤ) ^ x + U ^ 2) 0 := by
  have h1 : (2471 : ℕ) % 2 = 1 % 2 := by decide
  have hpow : (2471 : ℕ) ^ x % 2 = 1 := by
    rw [pow_mod_congr (b := 1) h1 x, Nat.one_pow]
  have hd : Cong 2 ((2471 : ℤ) ^ x) 1 := cong_of_nat_pow hpow
  have hs : Cong 2 (U ^ 2) 1 := by
    have hU' : Cong 2 U 1 := by unfold Cong; omega
    simpa using pow_cong hU' 2
  simpa using add_cong hd hs

/-! ## (ii) Translated Frey coefficients at 2

On `E : Y² = X³ + 2 U X² + W X` with `W = U² + 2471ˣ`, translate `X ↦ X+1`.
The note's case 4 takes `x` odd and `U` even; oddness of `x` is required
for `3 + 4U + W ≡ 2 (mod 4)`. -/

/-- `W = U² + 2471ˣ`. -/
def W (U : ℤ) (x : ℕ) : ℤ := U ^ 2 + (2471 : ℤ) ^ x

/-- `a₂'` after the translation. -/
def a2' (U : ℤ) : ℤ := 3 + 2 * U

/-- `a₄' = 3 + 4U + W`. -/
def a4' (U : ℤ) (x : ℕ) : ℤ := 3 + 4 * U + W U x

/-- `a₆' = (1+U)² + 2471ˣ`. -/
def a6' (U : ℤ) (x : ℕ) : ℤ := (1 + U) ^ 2 + (2471 : ℤ) ^ x

/-- `b₈' = 4 a₂' a₆' − (a₄')²` (`a₁' = a₃' = 0`). -/
def b8' (U : ℤ) (x : ℕ) : ℤ := 4 * a2' U * a6' U x - (a4' U x) ^ 2

private theorem even_sq_cong_four {U : ℤ} (hU : U % 2 = 0) : Cong 4 (U ^ 2) 0 := by
  have hmod : Cong 4 U 0 ∨ Cong 4 U 2 := by
    unfold Cong
    have hlt : U % 4 < 4 := Int.emod_lt_of_pos U (by norm_num)
    have hnn : 0 ≤ U % 4 := Int.emod_nonneg U (by norm_num)
    have heven : (U % 4) % 2 = 0 := by
      have : U % 2 = (U % 4) % 2 := by
        rw [← Int.emod_emod_of_dvd U (by decide : (2 : ℤ) ∣ 4)]
      omega
    omega
  rcases hmod with h | h <;> simpa using pow_cong h 2

private theorem base_pow_odd_cong_four {x : ℕ} (hx : x % 2 = 1) :
    Cong 4 ((2471 : ℤ) ^ x) 3 := by
  have hd : (2471 : ℕ) % 4 = 3 := by decide
  have d2 : (2471 : ℕ) ^ 2 % 4 = 1 := pow_mod_congr (b := 3) (m := 4) hd 2
  have odd : x = 2 * (x / 2) + 1 := by omega
  have hnat : (2471 : ℕ) ^ x % 4 = 3 := by
    conv => lhs; rw [odd, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod]
    rw [pow_mod_congr (b := 1) (m := 4) d2, Nat.one_pow, hd]
  exact cong_of_nat_pow hnat

private theorem base_pow_odd_cong_eight {x : ℕ} (hx : x % 2 = 1) :
    Cong 8 ((2471 : ℤ) ^ x) 7 := by
  have hd : (2471 : ℕ) % 8 = 7 := by decide
  have d2 : (2471 : ℕ) ^ 2 % 8 = 1 := pow_mod_congr (b := 7) (m := 8) hd 2
  have odd : x = 2 * (x / 2) + 1 := by omega
  have hnat : (2471 : ℕ) ^ x % 8 = 7 := by
    conv => lhs; rw [odd, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod]
    rw [pow_mod_congr (b := 1) (m := 8) d2, Nat.one_pow, hd]
  exact cong_of_nat_pow hnat

/-- Case 4 of the note: `3 + 4U + W ≡ 2 (mod 4)` for odd `x` and even `U`. -/
theorem a4'_mod_four {x : ℕ} {U : ℤ} (hx : x % 2 = 1) (hU : U % 2 = 0) :
    Cong 4 (a4' U x) 2 := by
  unfold a4' W
  have h3 : Cong 4 (3 : ℤ) 3 := rfl
  have h4U : Cong 4 (4 * U) 0 := by
    unfold Cong; rw [Int.mul_emod]; norm_num
  have hW : Cong 4 (U ^ 2 + (2471 : ℤ) ^ x) 3 := by
    simpa using add_cong (even_sq_cong_four hU) (base_pow_odd_cong_four hx)
  simpa using add_cong (add_cong h3 h4U) hW

/-- Case 4 of the note: `(1+U)² + 2471ˣ ≡ 0 (mod 8)` for odd `x` and even `U`. -/
theorem a6'_mod_eight {x : ℕ} {U : ℤ} (hx : x % 2 = 1) (hU : U % 2 = 0) :
    Cong 8 (a6' U x) 0 := by
  unfold a6'
  have hU8 : Cong 8 U 0 ∨ Cong 8 U 2 ∨ Cong 8 U 4 ∨ Cong 8 U 6 := by
    unfold Cong
    have hlt : U % 8 < 8 := Int.emod_lt_of_pos U (by norm_num)
    have hnn : 0 ≤ U % 8 := Int.emod_nonneg U (by norm_num)
    have heven : (U % 8) % 2 = 0 := by
      have : U % 2 = (U % 8) % 2 := by
        rw [← Int.emod_emod_of_dvd U (by decide : (2 : ℤ) ∣ 8)]
      omega
    omega
  have h1U : Cong 8 ((1 + U) ^ 2) 1 := by
    have h1 : Cong 8 (1 + U) 1 ∨ Cong 8 (1 + U) 3 ∨
        Cong 8 (1 + U) 5 ∨ Cong 8 (1 + U) 7 := by
      have h1const : Cong 8 (1 : ℤ) 1 := rfl
      rcases hU8 with h | h | h | h
      · left; exact add_cong h1const h
      · right; left; simpa using add_cong h1const h
      · right; right; left; simpa using add_cong h1const h
      · right; right; right; simpa using add_cong h1const h
    rcases h1 with h | h | h | h <;> simpa using pow_cong h 2
  simpa using add_cong h1U (base_pow_odd_cong_eight hx)

/-- Case 4 of the note: `b₈' ≡ 4 (mod 8)`. -/
theorem b8'_mod_eight {x : ℕ} {U : ℤ} (hx : x % 2 = 1) (hU : U % 2 = 0) :
    Cong 8 (b8' U x) 4 := by
  unfold b8' a2'
  have ha4 := a4'_mod_four (x := x) (U := U) hx hU
  have ha6 := a6'_mod_eight (x := x) (U := U) hx hU
  have ha4sq : Cong 8 ((a4' U x) ^ 2) 4 := by
    have hmod : Cong 8 (a4' U x) 2 ∨ Cong 8 (a4' U x) 6 := by
      unfold Cong at ha4 ⊢
      have hlt : a4' U x % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
      have hnn : 0 ≤ a4' U x % 8 := Int.emod_nonneg _ (by norm_num)
      have h4 : (a4' U x % 8) % 4 = 2 := by
        have : a4' U x % 4 = (a4' U x % 8) % 4 := by
          rw [← Int.emod_emod_of_dvd _ (by decide : (4 : ℤ) ∣ 8)]
        omega
      omega
    rcases hmod with h | h <;> simpa using pow_cong h 2
  have hprod : Cong 8 (4 * (3 + 2 * U) * a6' U x) 0 := by
    simpa using
      mul_cong (rfl : Cong 8 (4 * (3 + 2 * U)) (4 * (3 + 2 * U))) ha6
  simpa using sub_cong hprod ha4sq

/-- Equivalent form of `v₂(b₈') = 2`: divisible by `4` but not by `8`. -/
theorem b8'_valuation_two {x : ℕ} {U : ℤ} (hx : x % 2 = 1) (hU : U % 2 = 0) :
    (4 : ℤ) ∣ b8' U x ∧ ¬(8 : ℤ) ∣ b8' U x := by
  have h : Cong 8 (b8' U x) 4 := b8'_mod_eight hx hU
  unfold Cong at h
  refine ⟨?_, ?_⟩
  · have : b8' U x % 4 = 0 := by
      have : b8' U x % 4 = (b8' U x % 8) % 4 := by
        rw [← Int.emod_emod_of_dvd _ (by decide : (4 : ℤ) ∣ 8)]
      omega
    exact Int.dvd_iff_emod_eq_zero.mpr this
  · intro h8
    have : b8' U x % 8 = 0 := Int.emod_eq_zero_of_dvd h8
    omega

/-! ## (iii) Class-group relation of order 62 -/

/-- Case 2 of `docs/square-summand-2471.md`: in an additive commutative group
of order 62, if `31 • q = 0` and `2 • q = 31 • j`, then `q = 0`. -/
theorem class_relation_order_62 {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G = 62) {q j : G}
    (h31 : (31 : ℕ) • q = 0) (hrel : (2 : ℕ) • q = (31 : ℕ) • j) : q = 0 := by
  have h62 : (62 : ℕ) • j = 0 := by
    simpa [hcard] using (card_nsmul_eq_zero' (x := j) : (Nat.card G) • j = 0)
  have h4 : (4 : ℕ) • q = 0 := by
    calc
      (4 : ℕ) • q = (2 * 2 : ℕ) • q := by norm_num
      _ = (2 : ℕ) • ((2 : ℕ) • q) := by rw [mul_nsmul']
      _ = (2 : ℕ) • ((31 : ℕ) • j) := by rw [hrel]
      _ = (2 * 31 : ℕ) • j := by rw [← mul_nsmul']
      _ = (62 : ℕ) • j := by norm_num
      _ = 0 := h62
  have hgcd : ((4 : ℕ).gcd 31) • q = 0 := gcd_nsmul_eq_zero q h4 h31
  simpa using hgcd

end Beal.SquareSummand

#print axioms Beal.SquareSummand.sum_mod_sixteen_of_even_U
#print axioms Beal.SquareSummand.sum_even_of_odd_U
#print axioms Beal.SquareSummand.a4'_mod_four
#print axioms Beal.SquareSummand.a6'_mod_eight
#print axioms Beal.SquareSummand.b8'_valuation_two
#print axioms Beal.SquareSummand.class_relation_order_62
