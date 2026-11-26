import IdealDescent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.Associated
import Mathlib.Algebra.Ring.Basic

/-!
Mathlib ideal realization of `IdealAPI` on the monogenic order `ℤ[ω]`.

For fixed `D : ℤ`, an element `(re, im)` encodes `re + im·ω` with
`ω² = ω - D`. When `4D = d + 1` for squarefree `d ≡ 3 (mod 4)`
(equivalently field discriminant `-d ≡ 1 (mod 4)`), this order is the
full ring of integers `𝓞 K` of `K = ℚ(√-d)`. Both project bases
`d ∈ {167, 2471}` fall in that case (`D = 42` and `D = 618`).

This file equips the order with Mathlib's `CommRing` / `IsDomain`
instances and instantiates `IdealAPI` by `Ideal (OmegaRing D)` with
principal ideals `Ideal.span {·}`. Filling `DedekindGap` (conjugate
`(γ) = I^p`, the prime `P` above 2, and the class-group principalizer)
remains for a follow-up; no `sorry` and no new `axiom` are introduced.
-/
namespace Beal
open QuadraticBridge
open Beal.TwistIdentity
open Beal.IdealDescent

/-- The monogenic order `ℤ[ω]` with relation `ω² = ω - D`. -/
@[ext]
structure OmegaRing (D : Int) where
  /-- Coefficient of `1`. -/
  re : Int
  /-- Coefficient of `ω`. -/
  im : Int
  deriving DecidableEq

namespace OmegaRing

variable {D : Int}

/-- Convert the project's `Element` encoding into `OmegaRing`. -/
def ofElement (x : Element) : OmegaRing D := ⟨x.1, x.2⟩

/-- Convert back to the project's `Element` encoding. -/
def toElement (x : OmegaRing D) : Element := (x.re, x.im)

@[simp] theorem ofElement_toElement (x : OmegaRing D) : ofElement (toElement x) = x := rfl
@[simp] theorem toElement_ofElement (x : Element) : toElement (ofElement (D := D) x) = x := rfl

theorem toElement_injective : Function.Injective (toElement (D := D)) := by
  intro x y h
  cases x; cases y
  injection h with h1 h2
  simp_all

instance : Zero (OmegaRing D) := ⟨⟨0, 0⟩⟩
instance : One (OmegaRing D) := ⟨⟨1, 0⟩⟩
instance : Neg (OmegaRing D) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Add (OmegaRing D) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul (OmegaRing D) :=
  ⟨fun z w => ⟨z.re * w.re - D * z.im * w.im,
               z.re * w.im + z.im * w.re + z.im * w.im⟩⟩

@[simp] theorem zero_re : (0 : OmegaRing D).re = 0 := rfl
@[simp] theorem zero_im : (0 : OmegaRing D).im = 0 := rfl
@[simp] theorem one_re : (1 : OmegaRing D).re = 1 := rfl
@[simp] theorem one_im : (1 : OmegaRing D).im = 0 := rfl
@[simp] theorem neg_re (z : OmegaRing D) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : OmegaRing D) : (-z).im = -z.im := rfl
@[simp] theorem add_re (z w : OmegaRing D) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : OmegaRing D) : (z + w).im = z.im + w.im := rfl
@[simp] theorem mul_re (z w : OmegaRing D) :
    (z * w).re = z.re * w.re - D * z.im * w.im := rfl
@[simp] theorem mul_im (z w : OmegaRing D) :
    (z * w).im = z.re * w.im + z.im * w.re + z.im * w.im := rfl

theorem toElement_mul (x y : OmegaRing D) :
    toElement (x * y) = mul D (toElement x) (toElement y) := rfl

/-- Quadratic form on the order; matches `QuadraticBridge.norm`. -/
def qnorm (x : OmegaRing D) : Int := QuadraticBridge.norm D (toElement x)

theorem qnorm_eq (x : OmegaRing D) :
    qnorm x = x.re * x.re + x.re * x.im + D * x.im * x.im := rfl

theorem qnorm_mul (x y : OmegaRing D) : qnorm (x * y) = qnorm x * qnorm y := by
  simpa [qnorm, toElement_mul] using IdealDescent.norm_mul D (toElement x) (toElement y)

@[simp] theorem qnorm_one : qnorm (1 : OmegaRing D) = 1 := by
  simp [qnorm, toElement, QuadraticBridge.norm]

@[simp] theorem qnorm_zero : qnorm (0 : OmegaRing D) = 0 := by
  simp [qnorm, toElement, QuadraticBridge.norm]

instance addCommGroup : AddCommGroup (OmegaRing D) := by
  refine
  { add := (· + ·)
    zero := (0 : OmegaRing D)
    sub := fun a b => a + -b
    neg := Neg.neg
    nsmul := @nsmulRec (OmegaRing D) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (OmegaRing D) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
      (@nsmulRec (OmegaRing D) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;> ext <;> simp [add_comm, add_left_comm]

instance addGroupWithOne : AddGroupWithOne (OmegaRing D) :=
  { addCommGroup with
    natCast := fun n => ⟨(n : Int), 0⟩
    intCast := fun n => ⟨n, 0⟩
    one := 1 }

instance commRing : CommRing (OmegaRing D) := by
  refine
  { addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec (OmegaRing D) ⟨1⟩ ⟨(· * ·)⟩
    add_comm := add_comm
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

/-- Positive-definite `d = 4D - 1 > 0` forces vanishing norm to imply zero. -/
theorem qnorm_eq_zero_iff (hd : (0 : Int) < 4 * D - 1) {x : OmegaRing D} :
    qnorm x = 0 ↔ x = 0 := by
  constructor
  · intro hN
    have h4 := IdealDescent.four_mul_norm D (toElement x)
    change (4 : Int) * qnorm x =
        (2 * x.re + x.im) ^ 2 + (4 * D - 1) * x.im ^ 2 at h4
    rw [hN] at h4
    have hy0 : x.im = 0 := by
      by_contra hy
      have : (1 : Int) ≤ x.im ^ 2 := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg (2 * x.re + x.im)]
    have hx0 : x.re = 0 := by
      have : (4 : Int) * 0 = (2 * x.re + x.im) ^ 2 + (4 * D - 1) * x.im ^ 2 := h4
      simp [hy0] at this
      nlinarith
    ext <;> simp [hx0, hy0]
  · intro hx; simp [hx]

theorem qnorm_nonneg (hd : (0 : Int) < 4 * D - 1) (x : OmegaRing D) :
    (0 : Int) ≤ qnorm x := by
  have h4 := IdealDescent.four_mul_norm D (toElement x)
  change (4 : Int) * qnorm x =
      (2 * x.re + x.im) ^ 2 + (4 * D - 1) * x.im ^ 2 at h4
  nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg x.im]

theorem noZeroDivisors (hd : (0 : Int) < 4 * D - 1) :
    NoZeroDivisors (OmegaRing D) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hN : qnorm a * qnorm b = 0 := by
      have := congrArg qnorm hab
      simpa [qnorm_mul, qnorm_zero] using this
    rcases Int.eq_zero_or_eq_zero_of_mul_eq_zero hN with ha | hb
    · left; exact (qnorm_eq_zero_iff hd).mp ha
    · right; exact (qnorm_eq_zero_iff hd).mp hb

instance nontrivial : Nontrivial (OmegaRing D) :=
  ⟨⟨0, 1, fun h => by
    have : (0 : Int) = 1 := congrArg OmegaRing.re h
    cases this⟩⟩

/-- Under positive-definite discriminant the order is an integral domain. -/
theorem isDomain (hd : (0 : Int) < 4 * D - 1) : IsDomain (OmegaRing D) := by
  haveI := noZeroDivisors hd
  exact NoZeroDivisors.to_isDomain _

/-- Powers agree with `QuadraticBridge.pow` after `toElement`. -/
theorem toElement_pow (x : OmegaRing D) : ∀ n, toElement (x ^ n) = pow D (toElement x) n
  | 0 => by
    change toElement (1 : OmegaRing D) = (1, 0)
    rfl
  | n + 1 => by
    rw [pow_succ, toElement_mul, toElement_pow x n]
    rfl

theorem isUnit_of_qnorm_one
    (hunits :
      ∀ u : Element, QuadraticBridge.norm D u = 1 →
        u = (1, 0) ∨ u = (-1, 0))
    {u : OmegaRing D} (hu : qnorm u = 1) : IsUnit u := by
  rcases hunits (toElement u) hu with h | h
  · have : u = 1 := by
      apply toElement_injective
      simpa [toElement] using h
    simp [this]
  · have : u = -1 := by
      apply toElement_injective
      cases u
      simp [toElement] at h ⊢
      exact h
    exact this ▸ (isUnit_one : IsUnit (1 : OmegaRing D)).neg

theorem qnorm_eq_one_of_isUnit
    (hd : (0 : Int) < 4 * D - 1)
    {u : OmegaRing D} (hu : IsUnit u) : qnorm u = 1 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hN : qnorm u * qnorm v = 1 := by
    have := congrArg qnorm hv
    simpa [qnorm_mul, qnorm_one] using this
  have hu0 : qnorm u ≠ 0 := by
    intro h
    have : (0 : Int) = 1 := by rw [← hN, h, zero_mul]
    exact absurd this (by decide)
  have hpos : (0 : Int) < qnorm u :=
    lt_of_le_of_ne (qnorm_nonneg hd u) (Ne.symm hu0)
  have : qnorm u ∣ (1 : Int) := ⟨qnorm v, hN.symm⟩
  exact Int.eq_one_of_dvd_one (le_of_lt hpos) this

/-- Mathlib ideals of `OmegaRing D` realize `IdealAPI`, after transporting
`Element` coefficients through `ofElement`. -/
noncomputable def idealAPI
    (hd : (0 : Int) < 4 * D - 1)
    (hunits :
      ∀ u : Element, QuadraticBridge.norm D u = 1 →
        u = (1, 0) ∨ u = (-1, 0)) :
    IdealAPI D := by
  letI : IsDomain (OmegaRing D) := isDomain hd
  exact
  { Ideal := Ideal (OmegaRing D)
    principal := fun x => Ideal.span {ofElement (D := D) x}
    mulI := (· * ·)
    powI := (· ^ ·)
    mulI_comm := fun A B => mul_comm A B
    mulI_assoc := fun A B C => mul_assoc A B C
    principal_mul := by
      intro x y
      have hmul :
          ofElement (D := D) (mul D x y) =
            ofElement (D := D) x * ofElement (D := D) y := by
        ext <;> simp [ofElement, mul]
      rw [hmul, Ideal.span_singleton_mul_span_singleton]
    principal_pow := by
      intro x n
      have hpow :
          ofElement (D := D) (pow D x n) = (ofElement (D := D) x) ^ n := by
        apply toElement_injective
        simpa [toElement_ofElement] using
          (toElement_pow (ofElement (D := D) x) n).symm
      rw [hpow, Ideal.span_singleton_pow]
    powI_mul := by
      intro A B n
      exact mul_pow A B n
    powI_pow := by
      intro A m n
      exact (pow_mul A m n).symm
    principal_unit := by
      intro u x hu
      have hun : IsUnit (ofElement (D := D) u) :=
        isUnit_of_qnorm_one hunits (by simpa [qnorm, toElement_ofElement] using hu)
      have :
          ofElement (D := D) (mul D u x) =
            ofElement (D := D) u * ofElement (D := D) x := by
        ext <;> simp [ofElement, mul]
      rw [this, Ideal.span_singleton_mul_left_unit hun]
    principal_of_eq := by
      intro x y hxy
      have hAssoc :
          Associated (ofElement (D := D) x) (ofElement (D := D) y) :=
        (Ideal.span_singleton_eq_span_singleton).mp hxy
      obtain ⟨u, hu⟩ := hAssoc
      refine ⟨toElement (u : OmegaRing D), ?_, ?_⟩
      · have : qnorm (u : OmegaRing D) = 1 :=
          qnorm_eq_one_of_isUnit hd u.isUnit
        simpa [qnorm] using this
      · have hcomm : (u : OmegaRing D) * ofElement (D := D) x =
            ofElement (D := D) y := by
          simpa [mul_comm] using hu
        have := congrArg toElement hcomm
        simpa [toElement_mul, toElement_ofElement, mul] using this }

/-- Specialized `IdealAPI` for the 167 order (`D = 42`). -/
noncomputable def idealAPI167 : IdealAPI 42 :=
  idealAPI (D := 42) (by decide) units_pm_one_167

/-- Specialized `IdealAPI` for the 2471 order (`D = 618`). -/
noncomputable def idealAPI2471 : IdealAPI 618 :=
  idealAPI (D := 618) (by decide) units_pm_one_2471

/-- Norm of `γ` is a perfect `p`th power from the Diophantine equation.
This is the ring-level input to the still-open Dedekind perfect-power step. -/
theorem gamma_norm_is_pth_power
    {d : Nat} {D b c : Int} {x p : Nat}
    (hD : 4 * D = (d : Int) + 1) (hx : x % 2 = 1)
    (eqn : (d : Int)^x + b^4 = c^p) :
    QuadraticBridge.norm D (gammaOf ((d : Int)^((x - 1) / 2)) b) = c^p :=
  TwistIdentity.norm_gammaOf_solution hD hx eqn

/-- Conjugate of `a + b ω` in the integral basis (send `ω ↦ 1 - ω`,
i.e. `s ↦ -s`). -/
def conjugate (x : OmegaRing D) : OmegaRing D :=
  ⟨x.re + x.im, -x.im⟩

@[simp] theorem conjugate_re (x : OmegaRing D) : (conjugate x).re = x.re + x.im := rfl
@[simp] theorem conjugate_im (x : OmegaRing D) : (conjugate x).im = -x.im := rfl

theorem conjugate_mul (x y : OmegaRing D) :
    conjugate (x * y) = conjugate x * conjugate y := by
  ext <;> simp <;> ring

theorem conjugate_conjugate (x : OmegaRing D) : conjugate (conjugate x) = x := by
  ext <;> simp

/-- Product with the conjugate equals the rational integer `qnorm x`. -/
theorem mul_conjugate_eq_qnorm (x : OmegaRing D) :
    x * conjugate x = ⟨qnorm x, 0⟩ := by
  ext <;> simp [qnorm_eq] <;> ring

/-- Principal ideals multiply under conjugation as expected from the norm. -/
theorem span_mul_conjugate (x : OmegaRing D) :
    Ideal.span {x} * Ideal.span {conjugate x} =
      Ideal.span ({⟨qnorm x, 0⟩} : Set (OmegaRing D)) := by
  rw [Ideal.span_singleton_mul_span_singleton, mul_conjugate_eq_qnorm]

/-! ## Front doors specialized to the Mathlib API

The cubic exclusions below still require a `DedekindGap` certificate; the
`IdealAPI` argument is now the concrete Mathlib realization above.
-/

/-- `IdealFrontDoor` for `d = 167` once a Dedekind gap certificate is supplied. -/
noncomputable def frontDoor167_mathlib
    (gap : DedekindGap 167 11 42 eta167 idealAPI167) :
    IdealFrontDoor 167 11 42 eta167 :=
  frontDoor167 idealAPI167 gap

/-- `IdealFrontDoor` for `d = 2471` once a Dedekind gap certificate is supplied. -/
noncomputable def frontDoor2471_mathlib
    (gap : DedekindGap 2471 31 618 eta2471 idealAPI2471) :
    IdealFrontDoor 2471 31 618 eta2471 :=
  frontDoor2471 idealAPI2471 gap

/-- Cubic exclusion at 167, with Mathlib `IdealAPI` fixed and only the
Dedekind gap remaining as a hypothesis. -/
theorem no_integral_twist167_of_mathlib_gap
    (gap : DedekindGap 167 11 42 eta167 idealAPI167)
    (b c : Int) (eqn : (167 : Int) ^ 3 + b ^ 4 = c ^ 11) : False :=
  no_integral_twist167_of_gap idealAPI167 gap b c eqn

/-- Cubic exclusion at 2471, with Mathlib `IdealAPI` fixed and only the
Dedekind gap remaining as a hypothesis. -/
theorem no_integral_twist2471_of_mathlib_gap
    (gap : DedekindGap 2471 31 618 eta2471 idealAPI2471)
    (b c : Int) (eqn : (2471 : Int) ^ 3 + b ^ 4 = c ^ 31) : False :=
  no_integral_twist2471_of_gap idealAPI2471 gap b c eqn

end OmegaRing
end Beal

#print axioms Beal.OmegaRing.idealAPI167
#print axioms Beal.OmegaRing.idealAPI2471
#print axioms Beal.OmegaRing.gamma_norm_is_pth_power
#print axioms Beal.OmegaRing.mul_conjugate_eq_qnorm
#print axioms Beal.OmegaRing.no_integral_twist167_of_mathlib_gap
#print axioms Beal.OmegaRing.no_integral_twist2471_of_mathlib_gap
