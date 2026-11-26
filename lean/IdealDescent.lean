import TwistIdentity
import Mathlib.Tactic

/-!
Dedekind / class-group steps for the twist-identity front door.

Mathlib is pinned (`v4.19.0`) for tactics and as the intended home for a
future realization of `IdealAPI`. This file proves the finite / ring facts
and packages the remaining Dedekind obligations so that filling
`DedekindGap` yields `IdealFrontDoor.signed_twist` for both bases.

Paper steps from `docs/descent.md`:
1. conjugate coprimality of `(γ)` and `(γ̄)`
2. Dedekind UFD ⇒ `(γ) = I^p`
3. `P^p = (η)` with `[P]` of order `p` (no element of norm 2)
4. `[P]` generates `Cl(K)[p]` (class number / `p ‖ h`)
5. ∃ `k` with `I P^k = (β)`
6. raise: `(β^p) = (η^k γ)`
7. units `{±1}` ⇒ signed ring identity

Proved here: (3) ring side, (4) reduced-form class counts and exact `p`-power,
(7) units, integer support for (1), and composition of a `DedekindGap`
certificate into `IdealFrontDoor`. Remaining: realize (1)(2)(5)(6) by
instantiating `IdealAPI` / `DedekindGap` (Mathlib ideals of `𝓞 K`).
-/
namespace Beal.IdealDescent
open QuadraticBridge
open Beal.TwistIdentity

/-! ## Norm algebra -/

theorem four_mul_norm (D : Int) (u : Element) :
    (4 : Int) * QuadraticBridge.norm D u =
      (2 * u.1 + u.2)^2 + (4 * D - 1) * u.2^2 := by
  cases u with | mk x y =>
  change (4 : Int) * (x * x + x * y + D * y * y) =
    (2 * x + y) ^ 2 + (4 * D - 1) * y ^ 2
  ring

theorem norm_mul (D : Int) (u v : Element) :
    QuadraticBridge.norm D (mul D u v) =
      QuadraticBridge.norm D u * QuadraticBridge.norm D v := by
  cases u with | mk a b =>
  cases v with | mk c d =>
  change QuadraticBridge.norm D (a * c - D * b * d, a * d + b * c + b * d) =
    (a * a + a * b + D * b * b) * (c * c + c * d + D * d * d)
  simp only [QuadraticBridge.norm]
  ring

theorem norm_pow (D : Int) (u : Element) :
    ∀ n, QuadraticBridge.norm D (pow D u n) = (QuadraticBridge.norm D u)^n
  | 0 => by
    change QuadraticBridge.norm D (1, 0) = (QuadraticBridge.norm D u)^0
    simp [QuadraticBridge.norm]
  | n + 1 => by
    rw [pow, norm_mul, norm_pow D u n, pow_succ]

theorem mul_one (D : Int) (u : Element) : mul D (1, 0) u = u := by
  cases u; simp [mul]

theorem mul_neg_one (D : Int) (u : Element) : mul D (-1, 0) u = neg u := by
  cases u; simp [mul, neg]

/-! ## Step 7: unit group `{±1}` -/

theorem units_pm_one_of_disc {d : Nat} {D : Int}
    (hD : 4 * D = (d : Int) + 1) (hd : 5 ≤ d)
    (u : Element) (hN : QuadraticBridge.norm D u = 1) :
    u = (1, 0) ∨ u = (-1, 0) := by
  have h4 := four_mul_norm D u
  have hdisc : (4 : Int) * D - 1 = d := by omega
  rw [hN, hdisc] at h4
  have hd' : (5 : Int) ≤ d := by exact_mod_cast hd
  have hy0 : u.2 = 0 := by
    by_contra hy
    have : (1 : Int) ≤ u.2 ^ 2 := sq_pos_of_ne_zero hy
    have : (5 : Int) ≤ (d : Int) * u.2 ^ 2 := by nlinarith
    nlinarith [sq_nonneg (2 * u.1 + u.2)]
  have hx : u.1 ^ 2 = 1 := by
    have : (4 : Int) * 1 = (2 * u.1 + u.2) ^ 2 + (d : Int) * u.2 ^ 2 := h4
    simp [hy0] at this
    nlinarith
  have hpm : u.1 = 1 ∨ u.1 = -1 := (sq_eq_one_iff).mp hx
  rcases hpm with h | h
  · left; cases u; simp_all
  · right; cases u; simp_all

theorem units_pm_one_167 (u : Element) (hN : QuadraticBridge.norm 42 u = 1) :
    u = (1, 0) ∨ u = (-1, 0) :=
  units_pm_one_of_disc (d := 167) (D := 42) (by decide) (by decide) u hN

theorem units_pm_one_2471 (u : Element) (hN : QuadraticBridge.norm 618 u = 1) :
    u = (1, 0) ∨ u = (-1, 0) :=
  units_pm_one_of_disc (d := 2471) (D := 618) (by decide) (by decide) u hN

/-- Step 7 ring side: a unit associate yields a signed twist identity. -/
theorem signed_of_unit_associate {D : Int} {beta eta gamma : Element} {p k : Nat}
    (hunits :
      ∀ u : Element, QuadraticBridge.norm D u = 1 → u = (1, 0) ∨ u = (-1, 0))
    (u : Element) (hu : QuadraticBridge.norm D u = 1)
    (h : mul D u (pow D beta p) = mul D (pow D eta k) gamma) :
    pow D beta p = mul D (pow D eta k) gamma
      ∨ pow D beta p = neg (mul D (pow D eta k) gamma) := by
  rcases hunits u hu with rfl | rfl
  · left; simpa [mul_one] using h
  · right
    have h' : neg (pow D beta p) = mul D (pow D eta k) gamma := by
      simpa [mul_neg_one] using h
    -- Apply `neg` to both sides: `β^p = - η^k γ`.
    have hneg := congrArg neg h'
    simpa [neg_neg] using hneg

/-! ## Step 3 (ring side): no element of norm 2 -/

theorem no_norm_two_equation {d : Nat} (hd : 8 < d) (u v : Int) :
    u ^ 2 + (d : Int) * v ^ 2 ≠ 8 := by
  intro h
  by_cases hv : v = 0
  · subst hv
    have hu : u ^ 2 = 8 := by omega
    have h₁ : u ≤ 3 := by nlinarith
    have h₂ : -3 ≤ u := by nlinarith
    interval_cases u <;> simp at hu
  · have : (1 : Int) ≤ v ^ 2 := sq_pos_of_ne_zero hv
    nlinarith

theorem no_norm_two_167 (u v : Int) : u^2 + (167 : Int) * v^2 ≠ 8 :=
  no_norm_two_equation (d := 167) (by decide) u v

theorem no_norm_two_2471 (u v : Int) : u^2 + (2471 : Int) * v^2 ≠ 8 :=
  no_norm_two_equation (d := 2471) (by decide) u v

/-- Trace of `x + y ω` equals `2x + y`. -/
def trace (u : Element) : Int := 2 * u.1 + u.2

theorem eta167_odd_trace : trace eta167 % 2 = 1 := by decide
theorem eta2471_odd_trace : trace eta2471 % 2 = 1 := by decide
theorem eta167_odd_coeff : eta167.2 % 2 = 1 := by decide
theorem eta2471_odd_coeff : eta2471.2 % 2 = 1 := by decide

/-! ## Step 4 (computational): reduced-form class numbers -/

/-- Primitive reduced positive-definite form of discriminant `-d`.
Matches `scripts/check_twists.py`. -/
def isReducedForm (d : Nat) (a : Nat) (b : Int) (c : Nat) : Bool :=
  let disc : Int := -((d : Int))
  decide (0 < a) &&
  decide ((b : Int) * b - disc = 4 * (a : Int) * (c : Int)) &&
  decide (a ≤ c) &&
  decide (Int.natAbs b ≤ a) &&
  decide (Nat.gcd a (Nat.gcd b.natAbs c) = 1) &&
  !(decide (b < 0) && (decide (Int.natAbs b = a) || decide (a = c)))

/-- Bound `⌊√(d/3)⌋` on the leading coefficient of a reduced form. -/
def reducedAMax (d : Nat) : Nat := Nat.sqrt (d / 3)

def reducedForms (d : Nat) : List (Nat × Int × Nat) :=
  (List.range (reducedAMax d)).flatMap fun a0 =>
    let a := a0 + 1
    (List.range (2 * a + 1)).filterMap fun i =>
      let b : Int := (i : Int) - (a : Int)
      let num : Int := b * b + (d : Int)
      if num % (4 * (a : Int)) = 0 then
        let cInt := num / (4 * (a : Int))
        if 0 ≤ cInt then
          let c := cInt.toNat
          if isReducedForm d a b c then some (a, b, c) else none
        else none
      else none

def reducedFormCount (d : Nat) : Nat := (reducedForms d).length

set_option maxHeartbeats 800000

theorem class_number_167 : reducedFormCount 167 = 11 := by native_decide
theorem class_number_2471 : reducedFormCount 2471 = 62 := by native_decide

theorem p_exact_divides_class_number_167 :
    11 ∣ reducedFormCount 167 ∧ ¬(11 * 11 ∣ reducedFormCount 167) := by
  rw [class_number_167]; decide

theorem p_exact_divides_class_number_2471 :
    31 ∣ reducedFormCount 2471 ∧ ¬(31 * 31 ∣ reducedFormCount 2471) := by
  rw [class_number_2471]; decide

/-! ## Integer-side support for step 1 -/

theorem coprime_odd_two {c : Nat} (hc : c % 2 = 1) : Nat.Coprime c 2 := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  simp [hc]

theorem gcd_c_two_d {c d : Nat} (hc : c % 2 = 1) (hcd : Nat.Coprime c d) :
    Nat.Coprime c (2 * d) :=
  (coprime_odd_two hc).mul_right hcd

/-! ## Abstract Dedekind API

`OmegaRing.lean` realizes `IdealAPI` by Mathlib ideals of the monogenic
order `ℤ[ω]` (`Ideal (OmegaRing D)`), which is `𝓞 K` for the project
bases. The remaining Dedekind / class-group fields live in `DedekindGap`.
-/

/-- Minimal ideal operations for steps 1–6. Instantiate via Mathlib's
ideals of `𝓞 K` (see `OmegaRing.idealAPI167` / `idealAPI2471`), or
supply an external certificate. -/
structure IdealAPI (D : Int) where
  Ideal : Type
  principal : Element → Ideal
  mulI : Ideal → Ideal → Ideal
  powI : Ideal → Nat → Ideal
  mulI_comm : ∀ A B, mulI A B = mulI B A
  mulI_assoc : ∀ A B C, mulI (mulI A B) C = mulI A (mulI B C)
  principal_mul :
    ∀ x y, principal (mul D x y) = mulI (principal x) (principal y)
  principal_pow :
    ∀ x n, principal (pow D x n) = powI (principal x) n
  powI_mul :
    ∀ A B n, powI (mulI A B) n = mulI (powI A n) (powI B n)
  powI_pow :
    ∀ A m n, powI (powI A m) n = powI A (m * n)
  principal_unit :
    ∀ u x, QuadraticBridge.norm D u = 1 →
      principal (mul D u x) = principal x
  principal_of_eq :
    ∀ x y, principal x = principal y →
      ∃ u, QuadraticBridge.norm D u = 1 ∧ mul D u x = y

/-- Remaining Dedekind / class-group facts (paper steps 1–2 and 5–6, with
step 3's ideal `P` and step 4's generation folded into `principalizer`). -/
structure DedekindGap
    (d p : Nat) (D : Int) (eta : Element) (api : IdealAPI D) where
  /-- Steps 1–2: conjugate coprimality + Dedekind UFD give `(γ) = I^p`. -/
  gamma_perfect_power :
    ∀ (b c : Int) (x : Nat),
      x % 2 = 1 →
      (d : Int)^x + b^4 = c^p →
      ∃ I : api.Ideal,
        api.powI I p = api.principal (gammaOf ((d : Int)^((x - 1) / 2)) b)
  /-- Step 3: a prime ideal `P ∣ 2` with `P^p = (η)`. -/
  P : api.Ideal
  eta_is_P_pow : api.powI P p = api.principal eta
  /-- Steps 4–5: `[P]` generates `Cl[p]`, so some `I P^k` is principal. -/
  principalizer :
    ∀ (I : api.Ideal),
      (∃ γ : Element, api.powI I p = api.principal γ) →
      ∃ (k : Nat) (beta : Element),
        k < p ∧ api.mulI I (api.powI P k) = api.principal beta

/-- Bundle of facts proved in this file for one fixed base. -/
structure FiniteClassData (d p : Nat) (D : Int) (eta : Element) where
  hD : 4 * D = (d : Int) + 1
  hp_odd : p % 2 = 1
  units_pm_one :
    ∀ u : Element, QuadraticBridge.norm D u = 1 → u = (1, 0) ∨ u = (-1, 0)
  no_norm_two : ∀ u v : Int, u ^ 2 + (d : Int) * v ^ 2 ≠ 8
  eta_odd_trace : (2 * eta.1 + eta.2) % 2 = 1
  class_number : reducedFormCount d = p ∨ reducedFormCount d = 2 * p
  p_exact : p ∣ reducedFormCount d ∧ ¬(p * p ∣ reducedFormCount d)

def finite167 : FiniteClassData 167 11 42 eta167 where
  hD := by decide
  hp_odd := by decide
  units_pm_one := units_pm_one_167
  no_norm_two := no_norm_two_167
  eta_odd_trace := eta167_odd_trace
  class_number := by rw [class_number_167]; exact Or.inl rfl
  p_exact := p_exact_divides_class_number_167

def finite2471 : FiniteClassData 2471 31 618 eta2471 where
  hD := by decide
  hp_odd := by decide
  units_pm_one := units_pm_one_2471
  no_norm_two := no_norm_two_2471
  eta_odd_trace := eta2471_odd_trace
  class_number := by rw [class_number_2471]; exact Or.inr (by decide)
  p_exact := p_exact_divides_class_number_2471

/-- From a Dedekind gap certificate and the finite class data, obtain the
front-door hypothesis `signed_twist`. -/
theorem idealFrontDoor_of_gap
    {d p : Nat} {D : Int} {eta : Element} {api : IdealAPI D}
    (fin : FiniteClassData d p D eta)
    (gap : DedekindGap d p D eta api) :
    IdealFrontDoor d p D eta where
  hD := fin.hD
  hp_odd := fin.hp_odd
  signed_twist := by
    intro b c x hx eqn
    obtain ⟨I, hI⟩ := gap.gamma_perfect_power b c x hx eqn
    obtain ⟨k, beta, hk, hbeta⟩ :=
      gap.principalizer I ⟨gammaOf ((d : Int)^((x - 1) / 2)) b, hI⟩
    have hpow :
        api.powI (api.mulI I (api.powI gap.P k)) p
          = api.principal (pow D beta p) := by
      rw [hbeta, api.principal_pow]
    have hsplit :
        api.powI (api.mulI I (api.powI gap.P k)) p
          = api.mulI (api.powI I p) (api.powI (api.powI gap.P k) p) :=
      api.powI_mul _ _ _
    have hP : api.powI (api.powI gap.P k) p = api.powI (api.principal eta) k := by
      rw [api.powI_pow, Nat.mul_comm, ← api.powI_pow, gap.eta_is_P_pow]
    have hη : api.powI (api.principal eta) k = api.principal (pow D eta k) :=
      (api.principal_pow eta k).symm
    have hγ :
        api.mulI (api.powI I p) (api.principal (pow D eta k))
          = api.principal
              (mul D (pow D eta k)
                (gammaOf ((d : Int)^((x - 1) / 2)) b)) := by
      rw [hI, api.mulI_comm, ← api.principal_mul]
    have heq :
        api.principal (pow D beta p)
          = api.principal
              (mul D (pow D eta k)
                (gammaOf ((d : Int)^((x - 1) / 2)) b)) := by
      calc
        api.principal (pow D beta p)
            = api.powI (api.mulI I (api.powI gap.P k)) p := hpow.symm
        _ = api.mulI (api.powI I p) (api.powI (api.powI gap.P k) p) := hsplit
        _ = api.mulI (api.powI I p) (api.powI (api.principal eta) k) := by rw [hP]
        _ = api.mulI (api.powI I p) (api.principal (pow D eta k)) := by rw [hη]
        _ = _ := hγ
    obtain ⟨u, hu, hus⟩ := api.principal_of_eq _ _ heq
    refine ⟨beta, k, hk, ?_⟩
    exact signed_of_unit_associate fin.units_pm_one u hu hus

/-- Specialized front door for `d = 167` given a Dedekind gap certificate. -/
def frontDoor167 (api : IdealAPI 42) (gap : DedekindGap 167 11 42 eta167 api) :
    IdealFrontDoor 167 11 42 eta167 :=
  idealFrontDoor_of_gap finite167 gap

/-- Specialized front door for `d = 2471` given a Dedekind gap certificate. -/
def frontDoor2471 (api : IdealAPI 618) (gap : DedekindGap 2471 31 618 eta2471 api) :
    IdealFrontDoor 2471 31 618 eta2471 :=
  idealFrontDoor_of_gap finite2471 gap

/-- With a gap certificate, the cubic exclusion follows for `d = 167`. -/
theorem no_integral_twist167_of_gap
    (api : IdealAPI 42) (gap : DedekindGap 167 11 42 eta167 api)
    (b c : Int) (eqn : (167 : Int) ^ 3 + b ^ 4 = c ^ 11) : False := by
  obtain ⟨beta, k, hk, h⟩ :=
    twist_identity_of_front_door (frontDoor167 api gap) b c 3 (by decide) eqn
  have hγ : gammaOf ((167 : Nat) : Int) b = gamma 167 b := gammaOf_cubic 167 b
  -- `(3-1)/2 = 1`, so the coefficient is `167`.
  have h' : pow 42 beta 11 = mul 42 (pow 42 eta167 k) (gamma 167 b) := by
    simpa [hγ] using h
  exact no_integral_twist167 b beta k hk h'

theorem no_integral_twist2471_of_gap
    (api : IdealAPI 618) (gap : DedekindGap 2471 31 618 eta2471 api)
    (b c : Int) (eqn : (2471 : Int) ^ 3 + b ^ 4 = c ^ 31) : False := by
  obtain ⟨beta, k, hk, h⟩ :=
    twist_identity_of_front_door (frontDoor2471 api gap) b c 3 (by decide) eqn
  have hγ : gammaOf ((2471 : Nat) : Int) b = gamma 2471 b := gammaOf_cubic 2471 b
  have h' : pow 618 beta 31 = mul 618 (pow 618 eta2471 k) (gamma 2471 b) := by
    simpa [hγ] using h
  exact no_integral_twist2471 b beta k hk h'

end Beal.IdealDescent

#print axioms Beal.IdealDescent.units_pm_one_167
#print axioms Beal.IdealDescent.no_norm_two_167
#print axioms Beal.IdealDescent.class_number_167
#print axioms Beal.IdealDescent.class_number_2471
#print axioms Beal.IdealDescent.idealFrontDoor_of_gap
#print axioms Beal.IdealDescent.frontDoor167
#print axioms Beal.IdealDescent.no_integral_twist167_of_gap
