import QuadraticBridge

/-!
Ideal-theoretic front door toward the principalized twist identity.

The cubic certificates and `Forced683` already take
`β^p = η^k (b² + a s)` as a hypothesis in the integral basis `1, ω`.
This file formalizes the algebraic-integer steps that sit between a
primitive solution and that identity, and isolates the remaining
Dedekind / class-group obligations that still require Mathlib-scale
ideal arithmetic (or an external certificate).

Paper reference: `docs/descent.md` (“From an integer solution to a twist”)
and `docs/research-plan.md` §1 items 1–2.
-/
namespace Beal.TwistIdentity
open QuadraticBridge

/-- Negation in the integral basis. -/
def neg (u : Element) : Element := (-u.1, -u.2)

theorem neg_neg (u : Element) : neg (neg u) = u := by
  cases u; simp [neg]

theorem mul_neg_left (D : Int) (u v : Element) :
    mul D (neg u) v = neg (mul D u v) := by
  cases u; cases v
  simp only [mul, neg, Int.neg_mul, Int.mul_neg, Int.sub_neg, Int.neg_sub,
    Int.neg_add, Int.add_comm, ← Int.sub_eq_add_neg]

theorem mul_neg_right (D : Int) (u v : Element) :
    mul D u (neg v) = neg (mul D u v) := by
  cases u; cases v
  simp only [mul, neg, Int.neg_mul, Int.mul_neg, Int.sub_neg, Int.neg_sub,
    Int.neg_add, Int.add_comm, Int.sub_eq_add_neg]

private theorem pow_neg_even (D : Int) (u : Element) :
    ∀ m, pow D (neg u) (2 * m) = pow D u (2 * m)
  | 0 => rfl
  | m + 1 => by
    have hneg :
        pow D (neg u) (2 * (m + 1))
          = mul D (mul D (pow D (neg u) (2 * m)) (neg u)) (neg u) := by
      simp [pow, Nat.mul_succ]
    have hpos :
        pow D u (2 * (m + 1))
          = mul D (mul D (pow D u (2 * m)) u) u := by
      simp [pow, Nat.mul_succ]
    rw [hneg, hpos, pow_neg_even D u m]
    rw [mul_neg_right (u := pow D u (2 * m))]
    rw [mul_neg_left, mul_neg_right, neg_neg]

/-- For odd exponent, `(-β)^p = - β^p`. -/
theorem pow_neg_of_odd (D : Int) (u : Element) (n : Nat) (hn : n % 2 = 1) :
    pow D (neg u) n = neg (pow D u n) := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  subst hm; clear hn
  show mul D (pow D (neg u) (2 * m)) (neg u)
      = neg (mul D (pow D u (2 * m)) u)
  rw [pow_neg_even, mul_neg_right]

/-- Absorb a unit sign into the principalizer when `p` is odd.
If `β^p = - η^k γ`, then `(-β)^p = η^k γ`. -/
theorem absorb_unit_sign {D : Int} {eta beta gamma : Element} {p k : Nat}
    (hp : p % 2 = 1)
    (h : pow D beta p = neg (mul D (pow D eta k) gamma)) :
    pow D (neg beta) p = mul D (pow D eta k) gamma := by
  rw [pow_neg_of_odd D beta p hp, h, neg_neg]

/-- `b² + a·s` in the integral basis `1, ω`, where `s = 2ω - 1`. -/
def gammaOf (a b : Int) : Element := (b^2 - a, 2 * a)

theorem gammaOf_cubic (d : Nat) (b : Int) : gammaOf (d : Int) b = gamma d b := rfl

/-- The bridge `η` for `d = 167` equals `(3 + 7 s)/2` in the `ω`-basis. -/
theorem eta167_trace_form : eta167 = (((3 : Int) - 7) / 2, 7) := by decide

/-- The bridge `η` for `d = 2471` equals `(90621 + 391 s)/2` in the `ω`-basis. -/
theorem eta2471_trace_form : eta2471 = (((90621 : Int) - 391) / 2, 391) := by decide

/-- Norm of `b² + a·s` equals `b⁴ + a²·d` when `4D = d + 1`. -/
theorem norm_gammaOf {d : Nat} {D a b : Int} (hD : 4 * D = (d : Int) + 1) :
    norm D (gammaOf a b) = b^4 + a * a * (d : Int) := by
  change (b^2 - a) * (b^2 - a) + (b^2 - a) * (2 * a) + D * (2 * a) * (2 * a) = _
  have h₄ : D + D + D + D = (d : Int) + 1 := by omega
  have h₂ : (2 : Int) * a = a + a := by omega
  rw [h₂]
  have t := congrArg (fun x : Int => x * a * a) h₄
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add, Int.pow_succ, Int.pow_zero,
    Int.one_mul, Int.mul_one, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at t ⊢
  omega

private theorem pow_two_mul (d : Int) (m : Nat) :
    d^(2 * m) = d^m * d^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlen : 2 * (m + 1) = 2 * m + 2 := by omega
    calc
      d^(2 * (m + 1)) = d^(2 * m + 2) := by rw [hlen]
      _ = d^(2 * m) * d * d := by
          rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl, Int.pow_succ, Int.pow_succ]
      _ = d^m * d^m * d * d := by rw [ih]
      _ = (d^m * d) * (d^m * d) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = d^(m + 1) * d^(m + 1) := by rw [← Int.pow_succ]

private theorem odd_pow_split (d : Int) (x : Nat) (hx : x % 2 = 1) :
    d^x = d^((x - 1) / 2) * d^((x - 1) / 2) * d := by
  obtain ⟨m, hm⟩ : ∃ m, x = 2 * m + 1 := ⟨(x - 1) / 2, by omega⟩
  have hm' : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm, Int.pow_succ, pow_two_mul, hm']

/-- Recover the Diophantine norm for a general odd exponent. -/
theorem norm_gammaOf_solution {d : Nat} {D b c : Int} {x p : Nat}
    (hD : 4 * D = (d : Int) + 1) (hx : x % 2 = 1)
    (eqn : (d : Int)^x + b^4 = c^p) :
    norm D (gammaOf ((d : Int)^((x - 1) / 2)) b) = c^p := by
  have hnorm := norm_gammaOf (d := d) (D := D) (a := (d : Int)^((x - 1) / 2)) (b := b) hD
  have hpow := odd_pow_split (d : Int) x hx
  calc
    norm D (gammaOf ((d : Int)^((x - 1) / 2)) b)
        = b^4 + (d : Int)^((x - 1) / 2) * (d : Int)^((x - 1) / 2) * (d : Int) := hnorm
    _ = b^4 + (d : Int)^x := by rw [← hpow]
    _ = (d : Int)^x + b^4 := by rw [Int.add_comm]
    _ = c^p := eqn

/-- Norms of the two principalizing elements η. -/
theorem norm_eta167 : norm 42 eta167 = (2 : Int)^11 := by decide
theorem norm_eta2471 : norm 618 eta2471 = (2 : Int)^31 := by decide

/-! ## Remaining ideal-theoretic obligations

The lemmas above close the purely algebraic-integer fragment of the front
door. The structure `IdealFrontDoor` packages the Dedekind / class-group
facts still taken from the paper proof in `docs/descent.md`.

See `IdealDescent.lean` for proved units `{±1}`, no-norm-two, class numbers,
and the `DedekindGap` → `IdealFrontDoor` composition. Still open there:
conjugate coprimality ⇒ `(γ) = I^p`, ideal `P` with `P^p = (η)`, and the
principalizer. Downstream: local periodicity `x ↦ x+4p` and the odd-residue sweep.
-/

/-- Hypotheses that turn a primitive solution into a signed twist identity. -/
structure IdealFrontDoor (d p : Nat) (D : Int) (eta : Element) where
  /-- Discriminant relation for the integral basis. -/
  hD : 4 * D = (d : Int) + 1
  /-- Odd prime exponent (used for unit absorption). -/
  hp_odd : p % 2 = 1
  /-- From `(γ) = I^p`, `P^p = (η)`, `[P]` generating `Cl[p]`, and
  `IP^k = (β)`, ideal arithmetic supplies a signed identity in the ring. -/
  signed_twist :
    ∀ (b c : Int) (x : Nat),
      x % 2 = 1 →
      (d : Int)^x + b^4 = c^p →
      ∃ (beta : Element) (k : Nat),
        k < p ∧
        (pow D beta p = mul D (pow D eta k) (gammaOf ((d : Int)^((x - 1) / 2)) b)
          ∨ pow D beta p
              = neg (mul D (pow D eta k) (gammaOf ((d : Int)^((x - 1) / 2)) b)))

/-- Signed identity plus odd `p` yields the unsigned bridge form. -/
theorem unsigned_twist_of_signed
    {D : Int} {eta beta gamma : Element} {p k : Nat}
    (hp : p % 2 = 1)
    (h : pow D beta p = mul D (pow D eta k) gamma
        ∨ pow D beta p = neg (mul D (pow D eta k) gamma)) :
    ∃ beta', pow D beta' p = mul D (pow D eta k) gamma := by
  rcases h with h | h
  · exact ⟨beta, h⟩
  · exact ⟨neg beta, absorb_unit_sign hp h⟩

/-- From the ideal front door, obtain the bridge-shaped twist identity. -/
theorem twist_identity_of_front_door
    {d p : Nat} {D : Int} {eta : Element}
    (door : IdealFrontDoor d p D eta)
    (b c : Int) (x : Nat) (hx : x % 2 = 1)
    (eqn : (d : Int)^x + b^4 = c^p) :
    ∃ (beta : Element) (k : Nat),
      k < p ∧
      pow D beta p
        = mul D (pow D eta k) (gammaOf ((d : Int)^((x - 1) / 2)) b) := by
  rcases door.signed_twist b c x hx eqn with ⟨beta, k, hk, hid⟩
  rcases unsigned_twist_of_signed door.hp_odd hid with ⟨beta', h'⟩
  exact ⟨beta', k, hk, h'⟩

/-- Specialize the cubic bridge input for `d = 167`. -/
theorem cubic_twist167_of_signed {beta : Element} {k : Nat} {b : Int}
    (h : pow 42 beta 11 = mul 42 (pow 42 eta167 k) (gamma 167 b)
        ∨ pow 42 beta 11 = neg (mul 42 (pow 42 eta167 k) (gamma 167 b))) :
    ∃ beta', pow 42 beta' 11 = mul 42 (pow 42 eta167 k) (gamma 167 b) :=
  unsigned_twist_of_signed (p := 11) (by decide) h

/-- Specialize the cubic bridge input for `d = 2471`. -/
theorem cubic_twist2471_of_signed {beta : Element} {k : Nat} {b : Int}
    (h : pow 618 beta 31 = mul 618 (pow 618 eta2471 k) (gamma 2471 b)
        ∨ pow 618 beta 31 = neg (mul 618 (pow 618 eta2471 k) (gamma 2471 b))) :
    ∃ beta', pow 618 beta' 31 = mul 618 (pow 618 eta2471 k) (gamma 2471 b) :=
  unsigned_twist_of_signed (p := 31) (by decide) h

/-- With a signed cubic twist and the existing certificate, obtain a contradiction. -/
theorem no_integral_twist167_of_signed (b : Int) (beta : Element) (k : Nat)
    (hk : k < 11)
    (h : pow 42 beta 11 = mul 42 (pow 42 eta167 k) (gamma 167 b)
        ∨ pow 42 beta 11 = neg (mul 42 (pow 42 eta167 k) (gamma 167 b))) :
    False := by
  rcases cubic_twist167_of_signed h with ⟨beta', h'⟩
  exact no_integral_twist167 b beta' k hk h'

theorem no_integral_twist2471_of_signed (b : Int) (beta : Element) (k : Nat)
    (hk : k < 31)
    (h : pow 618 beta 31 = mul 618 (pow 618 eta2471 k) (gamma 2471 b)
        ∨ pow 618 beta 31 = neg (mul 618 (pow 618 eta2471 k) (gamma 2471 b))) :
    False := by
  rcases cubic_twist2471_of_signed h with ⟨beta', h'⟩
  exact no_integral_twist2471 b beta' k hk h'

end Beal.TwistIdentity

#print axioms Beal.TwistIdentity.absorb_unit_sign
#print axioms Beal.TwistIdentity.norm_gammaOf_solution
#print axioms Beal.TwistIdentity.no_integral_twist167_of_signed
#print axioms Beal.TwistIdentity.no_integral_twist2471_of_signed
