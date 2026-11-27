import OmegaRing
import OmegaRingDedekind
import OmegaRingGamma
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic

/-!
# L2d: `P^p = (η)` with `[P]` of order `p`

Each project base has an element `η` of odd trace and norm `2^p`. The
principal ideals `(η)` and `(η̄)` are coprime, their product is `(2)^p`, and
Dedekind unique factorization yields `(η) = P^p` for an ideal `P` above 2.
The absence of norm-two elements forces `P` to be nonprincipal, so `[P]` has
order exactly `p`.

This fills `DedekindGap.eta_is_P_pow` for `idealAPI167` and `idealAPI2471`
(AGENTS L2d). L2e (`principalizer`) is separate.
-/

open Beal
open OmegaRing
open IdealDescent
open QuadraticBridge
open TwistIdentity
open OmegaRingGamma
open UniqueFactorizationMonoid

namespace Beal.OmegaRingEta

variable {D : ℤ}

/-! ## Auxiliary ring facts -/

def omTrace (x : OmegaRing D) : ℤ := 2 * x.re + x.im

theorem omTrace_ofElement (x : Element) :
    omTrace (ofElement (D := D) x) = IdealDescent.trace x := rfl

theorem add_conjugate (x : OmegaRing D) :
    x + conjugate x = ⟨omTrace x, 0⟩ := by
  refine OmegaRing.ext ?_ ?_
  · simp [omTrace]; ring
  · simp [omTrace]

theorem qnorm_pow (x : OmegaRing D) (n : ℕ) : qnorm (x ^ n) = qnorm x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, qnorm_mul, ih, pow_succ]

theorem qnorm_neg (x : OmegaRing D) : qnorm (-x) = qnorm x := by
  simp [qnorm_eq]

theorem Ideal.dvd_of_pow_dvd_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    {I J : Ideal A} {n : ℕ} (hn : 0 < n) (h : I ^ n ∣ J ^ n) : I ∣ J := by
  classical
  by_cases hJ : J = ⊥
  · subst hJ; exact dvd_zero _
  by_cases hI : I = ⊥
  · subst hI
    have hJn : J ^ n = ⊥ := by
      have hIn : (⊥ : Ideal A) ^ n = ⊥ := (pow_eq_zero_iff hn.ne').mpr rfl
      rw [hIn, ← Ideal.zero_eq_bot] at h
      simpa [Ideal.zero_eq_bot] using zero_dvd_iff.mp h
    have hJ0 : J = ⊥ :=
      (pow_eq_zero_iff hn.ne').mp (by simpa [Ideal.zero_eq_bot] using hJn)
    exact absurd hJ0 hJ
  refine (dvd_iff_normalizedFactors_le_normalizedFactors hI hJ).2 ?_
  have h' := (dvd_iff_normalizedFactors_le_normalizedFactors
    (pow_ne_zero n hI) (pow_ne_zero n hJ)).1 h
  rw [normalizedFactors_pow, normalizedFactors_pow] at h'
  refine (Multiset.le_iff_count).2 fun p => ?_
  have hc := (Multiset.le_iff_count.1 h') p
  simp only [Multiset.count_nsmul] at hc
  exact Nat.le_of_mul_le_mul_left hc hn

/-! ## Conjugate coprimality and `(η) = P^p` -/

theorem eta_mul_conjugate_eq_norm_pow {eta : Element} {p : ℕ}
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p) :
    ofElement (D := D) eta * conjugate (ofElement (D := D) eta) =
      ⟨(2 : ℤ) ^ p, 0⟩ := by
  have h := mul_conjugate_eq_qnorm (ofElement (D := D) eta)
  simpa [qnorm, toElement_ofElement, hN] using h

theorem span_eta_mul_conjugate_eq_two_pow {eta : Element} {p : ℕ}
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p) :
    Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)) *
        Ideal.span ({conjugate (ofElement (D := D) eta)} : Set (OmegaRing D)) =
      Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D)} : Set (OmegaRing D)) ^ p := by
  set η := ofElement (D := D) eta
  have hnorm : η * conjugate η = ⟨(2 : ℤ) ^ p, 0⟩ :=
    eta_mul_conjugate_eq_norm_pow hN
  calc
    Ideal.span {η} * Ideal.span {conjugate η}
        = Ideal.span ({⟨(2 : ℤ) ^ p, 0⟩} : Set (OmegaRing D)) := by
          rw [Ideal.span_singleton_mul_span_singleton, hnorm]
    _ = Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D) ^ p} : Set (OmegaRing D)) := by
          rw [intCast_pow]
    _ = Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D)} : Set (OmegaRing D)) ^ p :=
          (Ideal.span_singleton_pow _ _).symm

/-- Odd trace + norm `2^p` ⇒ `(η)` coprime to `(η̄)`. -/
theorem eta_conjugate_ideals_coprime {eta : Element} {p : ℕ}
    [IsDedekindDomain (OmegaRing D)]
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (htr : IdealDescent.trace eta % 2 = 1) :
    IsCoprime
      (Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)))
      (Ideal.span ({conjugate (ofElement (D := D) eta)} : Set (OmegaRing D))) := by
  set η := ofElement (D := D) eta
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hne
  haveI : M.IsPrime := Ideal.IsMaximal.isPrime hMmax
  have hη : η ∈ M :=
    (le_trans le_sup_left hMle) (Ideal.mem_span_singleton_self _)
  have hηb : conjugate η ∈ M :=
    (le_trans le_sup_right hMle) (Ideal.mem_span_singleton_self _)
  have htrM : (⟨omTrace η, 0⟩ : OmegaRing D) ∈ M := by
    have := add_mem hη hηb
    rwa [add_conjugate] at this
  have h2p : (⟨(2 : ℤ) ^ p, 0⟩ : OmegaRing D) ∈ M := by
    have hmul : η * conjugate η ∈ M * M := Ideal.mul_mem_mul hη hηb
    have : η * conjugate η ∈ M := Ideal.mul_le_left hmul
    rwa [eta_mul_conjugate_eq_norm_pow hN] at this
  have hcop : Int.gcd (omTrace η) ((2 : ℤ) ^ p) = 1 := by
    have hodd : (omTrace η) % 2 = 1 := by
      simpa [omTrace_ofElement] using htr
    have h2 : Nat.Coprime (omTrace η).natAbs 2 := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
      have : Odd (omTrace η) := Int.odd_iff.mpr hodd
      have : (omTrace η).natAbs % 2 = 1 :=
        Nat.odd_iff.mp (Int.natAbs_odd.mpr this)
      simp [this]
    have : Nat.Coprime (omTrace η).natAbs (2 ^ p) := h2.pow_right _
    simpa [Int.gcd, Int.natAbs_pow] using this
  have hab := Int.gcd_eq_gcd_ab (omTrace η) ((2 : ℤ) ^ p)
  rw [hcop, Nat.cast_one] at hab
  have hone : (1 : OmegaRing D) =
      ⟨omTrace η, 0⟩ * ⟨Int.gcdA (omTrace η) ((2 : ℤ) ^ p), 0⟩ +
        ⟨(2 : ℤ) ^ p, 0⟩ * ⟨Int.gcdB (omTrace η) ((2 : ℤ) ^ p), 0⟩ := by
    refine OmegaRing.ext ?_ ?_
    · simp [mul_re, mul_im, add_re, add_im]; linarith [hab]
    · simp [mul_re, mul_im, add_re, add_im]
  have : (1 : OmegaRing D) ∈ M := by
    rw [hone]
    exact add_mem (Ideal.mul_mem_right _ _ htrM)
      (Ideal.mul_mem_right _ _ h2p)
  exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

/-- Dedekind UFD: `(η) = P^p` for some ideal `P`. -/
theorem eta_is_perfect_power {eta : Element} {p : ℕ}
    [IsDedekindDomain (OmegaRing D)]
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (htr : IdealDescent.trace eta % 2 = 1) :
    ∃ P : Ideal (OmegaRing D),
      P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)) := by
  set η := ofElement (D := D) eta
  set A := Ideal.span ({η} : Set (OmegaRing D))
  set B := Ideal.span ({conjugate η} : Set (OmegaRing D))
  set C := Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D)} : Set (OmegaRing D))
  have hcop : IsCoprime A B := by
    simpa [A, B, η] using eta_conjugate_ideals_coprime (D := D) hN htr
  have hgcd : IsUnit (gcd A B) := by
    have h1 : gcd A B = 1 := (Ideal.isCoprime_iff_gcd).mp hcop
    simp [h1]
  have hmul : A * B = C ^ p := by
    simpa [A, B, C, η] using span_eta_mul_conjugate_eq_two_pow (D := D) hN
  obtain ⟨P, hP⟩ := exists_associated_pow_of_mul_eq_pow hgcd hmul
  exact ⟨P, (associated_iff_eq.mp hP).trans (by simp [A, η])⟩

/-- Any such `P` divides `(2)`, hence lies above 2. -/
theorem eta_pow_divides_two {eta : Element} {p : ℕ} {P : Ideal (OmegaRing D)}
    [IsDedekindDomain (OmegaRing D)]
    (hp : 0 < p)
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D))) :
    P ∣ Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D)} : Set (OmegaRing D)) := by
  set C := Ideal.span ({(⟨(2 : ℤ), 0⟩ : OmegaRing D)} : Set (OmegaRing D))
  set B := Ideal.span ({conjugate (ofElement (D := D) eta)} : Set (OmegaRing D))
  have hmul : Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)) * B = C ^ p :=
    span_eta_mul_conjugate_eq_two_pow (D := D) hN
  have : P ^ p ∣ C ^ p := ⟨B, by rw [hP]; exact hmul.symm⟩
  exact Ideal.dvd_of_pow_dvd_pow hp this

theorem two_mem_of_eta_pow {eta : Element} {p : ℕ} {P : Ideal (OmegaRing D)}
    [IsDedekindDomain (OmegaRing D)]
    (hp : 0 < p)
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D))) :
    (⟨(2 : ℤ), 0⟩ : OmegaRing D) ∈ P := by
  have hdiv := eta_pow_divides_two (D := D) hp hN hP
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hdiv)

/-! ## Order of `[P]` is exactly `p` -/

theorem four_mul_qnorm_eq_trace_form (x : OmegaRing D) :
    (4 : ℤ) * qnorm x = omTrace x ^ 2 + (4 * D - 1) * x.im ^ 2 := by
  simpa [qnorm, toElement, omTrace, IdealDescent.trace] using
    IdealDescent.four_mul_norm D (toElement x)

/-- `P^p = (η)` is never principal: a generator would have norm 2. -/
theorem not_principal_of_eta_pow {eta : Element} {p : ℕ} {P : Ideal (OmegaRing D)}
    [IsDomain (OmegaRing D)]
    (hd : (0 : ℤ) < 4 * D - 1) (hp : 0 < p) (hodd : Odd p)
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)))
    (hunits :
      ∀ u : Element, QuadraticBridge.norm D u = 1 →
        u = (1, 0) ∨ u = (-1, 0))
    (hnorm2 : ∀ t v : ℤ, t ^ 2 + (4 * D - 1) * v ^ 2 ≠ 8) :
    ¬ ∃ α : OmegaRing D, P = Ideal.span {α} := by
  rintro ⟨α, hα⟩
  have hsp : Ideal.span ({α ^ p} : Set (OmegaRing D)) =
      Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)) := by
    rw [← Ideal.span_singleton_pow, ← hα, hP]
  have hAssoc : Associated (α ^ p) (ofElement (D := D) eta) :=
    (Ideal.span_singleton_eq_span_singleton).mp hsp
  obtain ⟨u, hu⟩ := hAssoc
  -- `hu : α^p * ↑u = η`
  have hqU : qnorm (↑u : OmegaRing D) = 1 :=
    qnorm_eq_one_of_isUnit hd u.isUnit
  have hpm : (↑u : OmegaRing D) = 1 ∨ (↑u : OmegaRing D) = -1 := by
    have : toElement (↑u : OmegaRing D) = (1, 0) ∨
        toElement (↑u : OmegaRing D) = (-1, 0) :=
      hunits _ (by simpa [qnorm] using hqU)
    rcases this with h | h
    · left; exact toElement_injective (by simpa [toElement] using h)
    · right
      refine toElement_injective ?_
      simpa [toElement] using h
  have hqη : qnorm (ofElement (D := D) eta) = (2 : ℤ) ^ p := by
    simpa [qnorm, toElement_ofElement] using hN
  have hEq : α ^ p = ofElement (D := D) eta ∨
      α ^ p = -ofElement (D := D) eta := by
    rcases hpm with h1 | h1
    · left
      have : α ^ p * (↑u : OmegaRing D) = ofElement (D := D) eta := hu
      simpa [h1, mul_one] using this
    · right
      have : α ^ p * (↑u : OmegaRing D) = ofElement (D := D) eta := hu
      have : α ^ p * (-1) = ofElement (D := D) eta := by simpa [h1] using this
      have : -(α ^ p) = ofElement (D := D) eta := by simpa [mul_neg, mul_one] using this
      exact neg_eq_iff_eq_neg.mp this
  have hNα : qnorm α ^ p = (2 : ℤ) ^ p := by
    rcases hEq with h | h
    · simpa [qnorm_pow, hqη] using congrArg qnorm h
    · have := congrArg qnorm h
      simpa [qnorm_pow, qnorm_neg, hqη] using this
  have hα2 : qnorm α = 2 := by
    have hiff := (pow_eq_pow_iff_of_ne_zero hp.ne').mp hNα
    rcases hiff with h | ⟨_, heven⟩
    · exact h
    · exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
  have hform : omTrace α ^ 2 + (4 * D - 1) * α.im ^ 2 = 8 := by
    have := four_mul_qnorm_eq_trace_form (D := D) α
    linarith [this, hα2]
  exact (hnorm2 (omTrace α) α.im) hform

/-- For prime `p ≠ 2`, `P^p` principal and `P` nonprincipal imply that the
class of `P` has order exactly `p`. -/
theorem order_eq_p_of_eta_pow {eta : Element} {p : ℕ} {P : Ideal (OmegaRing D)}
    [IsDomain (OmegaRing D)]
    (hd : (0 : ℤ) < 4 * D - 1) (hp : Nat.Prime p) (h2 : p ≠ 2)
    (hN : QuadraticBridge.norm D eta = (2 : ℤ) ^ p)
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)))
    (hunits :
      ∀ u : Element, QuadraticBridge.norm D u = 1 →
        u = (1, 0) ∨ u = (-1, 0))
    (hnorm2 : ∀ t v : ℤ, t ^ 2 + (4 * D - 1) * v ^ 2 ≠ 8) :
    ¬ ∃ α : OmegaRing D, P = Ideal.span {α} :=
  not_principal_of_eta_pow hd hp.pos (hp.odd_of_ne_two h2) hN hP hunits hnorm2

/-! ## Project bases -/

theorem eta_is_P_pow_167 :
    ∃ P : Ideal (OmegaRing 42),
      P ^ 11 = Ideal.span ({ofElement (D := 42) eta167} : Set (OmegaRing 42)) :=
  eta_is_perfect_power (D := 42) norm_eta167 eta167_odd_trace

set_option maxRecDepth 4096 in
theorem eta_is_P_pow_2471 :
    ∃ P : Ideal (OmegaRing 618),
      P ^ 31 = Ideal.span ({ofElement (D := 618) eta2471} : Set (OmegaRing 618)) :=
  eta_is_perfect_power (D := 618) norm_eta2471 eta2471_odd_trace

/-- Explicit choice of `P` at `d = 167`. -/
noncomputable def P167 : Ideal (OmegaRing 42) :=
  Classical.choose eta_is_P_pow_167

theorem P167_pow : P167 ^ 11 =
    Ideal.span ({ofElement (D := 42) eta167} : Set (OmegaRing 42)) :=
  Classical.choose_spec eta_is_P_pow_167

theorem two_mem_P167 : (⟨(2 : ℤ), 0⟩ : OmegaRing 42) ∈ P167 :=
  two_mem_of_eta_pow (D := 42) (by decide : 0 < 11) norm_eta167 P167_pow

theorem P167_not_principal :
    ¬ ∃ α : OmegaRing 42, P167 = Ideal.span {α} :=
  not_principal_of_eta_pow (D := 42) (by decide : (0 : ℤ) < 4 * 42 - 1)
    (by decide : 0 < 11) (by decide : Odd 11) norm_eta167 P167_pow
    units_pm_one_167
    (fun t v => by
      have hdisc : (4 : ℤ) * 42 - 1 = 167 := by decide
      simpa [hdisc] using no_norm_two_167 t v)

/-- Explicit choice of `P` at `d = 2471`. -/
noncomputable def P2471 : Ideal (OmegaRing 618) :=
  Classical.choose eta_is_P_pow_2471

set_option maxRecDepth 4096 in
theorem P2471_pow : P2471 ^ 31 =
    Ideal.span ({ofElement (D := 618) eta2471} : Set (OmegaRing 618)) :=
  Classical.choose_spec eta_is_P_pow_2471

set_option maxRecDepth 4096 in
theorem two_mem_P2471 : (⟨(2 : ℤ), 0⟩ : OmegaRing 618) ∈ P2471 :=
  two_mem_of_eta_pow (D := 618) (by omega : 0 < 31) norm_eta2471 P2471_pow

set_option maxRecDepth 4096 in
theorem P2471_not_principal :
    ¬ ∃ α : OmegaRing 618, P2471 = Ideal.span {α} :=
  not_principal_of_eta_pow (D := 618) (by omega : (0 : ℤ) < 4 * 618 - 1)
    (by omega : 0 < 31) ⟨15, by omega⟩ norm_eta2471 P2471_pow
    units_pm_one_2471
    (fun t v => by
      have hdisc : (4 : ℤ) * 618 - 1 = 2471 := by native_decide
      simpa [hdisc] using no_norm_two_2471 t v)

/-! ## IdealAPI-shaped specializations -/

theorem eta_is_P_pow_idealAPI167 :
    ∃ P : idealAPI167.Ideal,
      idealAPI167.powI P 11 = idealAPI167.principal eta167 :=
  eta_is_P_pow_167

set_option maxRecDepth 4096 in
theorem eta_is_P_pow_idealAPI2471 :
    ∃ P : idealAPI2471.Ideal,
      idealAPI2471.powI P 31 = idealAPI2471.principal eta2471 :=
  eta_is_P_pow_2471

end Beal.OmegaRingEta

#print axioms Beal.OmegaRingEta.eta_is_P_pow_167
#print axioms Beal.OmegaRingEta.eta_is_P_pow_2471
#print axioms Beal.OmegaRingEta.P167_not_principal
#print axioms Beal.OmegaRingEta.P2471_not_principal
#print axioms Beal.OmegaRingEta.two_mem_P167
#print axioms Beal.OmegaRingEta.two_mem_P2471
