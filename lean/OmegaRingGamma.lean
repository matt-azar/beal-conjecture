import OmegaRing
import OmegaRingDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic

/-!
# L2c: conjugate coprimality and `(γ) = I^p`

Given a Beal-type equation `d^x + b^4 = c^p` with `x` odd and `gcd(b,d)=1`,
the principal ideals `(γ)` and `(γ̄)` in `OmegaRing D` are coprime, their
product is `(c)^p`, and Dedekind unique factorization yields `(γ) = I^p`.

This fills `DedekindGap.gamma_perfect_power` for `idealAPI167` and
`idealAPI2471` (AGENTS L2c). L2d (`eta_is_P_pow`) is separate.
-/

open Beal
open OmegaRing
open IdealDescent
open QuadraticBridge
open TwistIdentity

namespace Beal.OmegaRingGamma

variable {D : ℤ}

def sqrtNeg : OmegaRing D := ⟨-1, 2⟩

theorem sqrtNeg_sq {d : ℕ} (hD : 4 * D = (d : ℤ) + 1) :
    (sqrtNeg (D := D)) ^ 2 = ⟨(-(d : ℤ)), 0⟩ := by
  have hmul : sqrtNeg (D := D) * sqrtNeg = ⟨(1 : ℤ) - 4 * D, 0⟩ := by
    apply OmegaRing.ext
    · simp only [sqrtNeg, mul_re]; ring
    · simp only [sqrtNeg, mul_im]; ring
  have hD' : (1 : ℤ) - 4 * D = -(d : ℤ) := by omega
  rw [pow_two, hmul, hD']

theorem sub_conjugate (x : OmegaRing D) :
    x - conjugate x = ⟨x.im, 0⟩ * sqrtNeg (D := D) := by
  apply OmegaRing.ext
  · have L : (x - conjugate x).re = -x.im := by
      simp only [sub_eq_add_neg, add_re, neg_re, conjugate]; ring
    have R : (⟨x.im, 0⟩ * sqrtNeg (D := D)).re = -x.im := by
      simp only [sqrtNeg, mul_re]; ring
    exact L.trans R.symm
  · have L : (x - conjugate x).im = 2 * x.im := by
      simp only [sub_eq_add_neg, add_im, neg_im, conjugate]; ring
    have R : (⟨x.im, 0⟩ * sqrtNeg (D := D)).im = 2 * x.im := by
      simp only [sqrtNeg, mul_im]; ring
    exact L.trans R.symm

theorem sub_conjugate_sq {d : ℕ} (hD : 4 * D = (d : ℤ) + 1) (x : OmegaRing D) :
    (x - conjugate x) ^ 2 = ⟨(-(x.im ^ 2) * (d : ℤ)), 0⟩ := by
  rw [sub_conjugate, mul_pow, sqrtNeg_sq (D := D) hD]
  have hpow : (⟨x.im, 0⟩ : OmegaRing D) ^ 2 = ⟨x.im ^ 2, 0⟩ := by
    apply OmegaRing.ext
    · simp only [pow_two, mul_re]; ring
    · simp only [pow_two, mul_im]; ring
  rw [hpow]
  apply OmegaRing.ext
  · simp only [mul_re]; ring
  · simp only [mul_im]; ring

theorem gamma_sub_conjugate_sq {d : ℕ} (hD : 4 * D = (d : ℤ) + 1) (a b : ℤ) :
    (ofElement (D := D) (gammaOf a b) -
        conjugate (ofElement (D := D) (gammaOf a b))) ^ 2 =
      ⟨(- (4 : ℤ) * a ^ 2 * d), 0⟩ := by
  rw [sub_conjugate_sq (d := d) hD]
  have him : (ofElement (D := D) (gammaOf a b)).im = 2 * a := rfl
  rw [him]
  congr 1
  ring

theorem b4_eq_natAbs_pow (b : ℤ) : b ^ 4 = ((b.natAbs : ℤ) ^ 4) := by
  have h2 : b ^ 2 = (b.natAbs : ℤ) ^ 2 := by
    rw [pow_two, ← Int.natAbs_mul_self, pow_two, Nat.cast_mul]
  calc b ^ 4 = (b ^ 2) ^ 2 := by ring
    _ = ((b.natAbs : ℤ) ^ 2) ^ 2 := by rw [h2]
    _ = (b.natAbs : ℤ) ^ 4 := by ring

theorem c_nonneg_of_odd_pow {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd : 0 < d) (hodd : Odd p)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) : 0 ≤ c := by
  have hL : 0 ≤ (d : ℤ) ^ x + b ^ 4 := by
    have h1 : 0 ≤ (d : ℤ) ^ x := pow_nonneg (by exact_mod_cast (le_of_lt hd)) _
    have h2 : 0 ≤ b ^ 4 := by
      have : 0 ≤ (b ^ 2) ^ 2 := sq_nonneg _
      convert this using 1; ring
    nlinarith [h1, h2]
  have : 0 ≤ c ^ p := by rwa [← eqn]
  exact (hodd.pow_nonneg_iff).mp this

theorem eqn_natAbs {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd : 0 < d) (hodd : Odd p)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    d ^ x + b.natAbs ^ 4 = c.toNat ^ p := by
  have hc : 0 ≤ c := c_nonneg_of_odd_pow hd hodd eqn
  have eqn' : (d : ℤ) ^ x + (b.natAbs : ℤ) ^ 4 = (c.toNat : ℤ) ^ p := by
    rw [← b4_eq_natAbs_pow, Int.toNat_of_nonneg hc, eqn]
  exact_mod_cast eqn'

theorem right_base_odd_of_eqn {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd16 : d % 16 = 7) (hx : x % 2 = 1) (hp : 4 ≤ p) (hodd : Odd p)
    (hd : 0 < d)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) : c % 2 = 1 := by
  have eqnN := eqn_natAbs hd hodd eqn
  have hc0 : 0 ≤ c := c_nonneg_of_odd_pow hd hodd eqn
  have hoddN := right_base_is_odd (d := d) (b := b.natAbs) (c := c.toNat) hd16 hx hp eqnN
  have hc' : c = (c.toNat : ℤ) := (Int.toNat_of_nonneg hc0).symm
  rw [hc']
  exact_mod_cast hoddN

theorem gcd_b_c_eq_one {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd : 0 < d) (_hx : 0 < x) (hp : 0 < p) (hbd : Int.gcd b (d : ℤ) = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) : Int.gcd b c = 1 := by
  change Nat.gcd b.natAbs c.natAbs = 1
  by_contra hg
  have hne : Nat.gcd b.natAbs c.natAbs ≠ 0 := by
    intro h0
    obtain ⟨hb0, hc0⟩ := Nat.gcd_eq_zero_iff.mp h0
    have hb0' : b = 0 := Int.natAbs_eq_zero.mp hb0
    have hc0' : c = 0 := Int.natAbs_eq_zero.mp hc0
    subst hb0'; subst hc0'
    have : (d : ℤ) ^ x = 0 := by
      simpa [zero_pow hp.ne'] using eqn
    exact (pow_ne_zero x (Nat.cast_ne_zero.mpr (ne_of_gt hd))).elim this
  have hgpos : 0 < Nat.gcd b.natAbs c.natAbs := Nat.pos_of_ne_zero hne
  have hgt : 1 < Nat.gcd b.natAbs c.natAbs :=
    lt_of_le_of_ne (Nat.succ_le_of_lt hgpos) (Ne.symm hg)
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  have qb : q ∣ b.natAbs := hqg.trans (Nat.gcd_dvd_left _ _)
  have qc : q ∣ c.natAbs := hqg.trans (Nat.gcd_dvd_right _ _)
  have qbZ : (q : ℤ) ∣ b := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qb)
  have qcZ : (q : ℤ) ∣ c := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qc)
  have hq_dx : (q : ℤ) ∣ (d : ℤ) ^ x := by
    have : (d : ℤ) ^ x = c ^ p - b ^ 4 := by linear_combination eqn
    rw [this]
    exact dvd_sub (dvd_pow qcZ hp.ne') (dvd_pow qbZ (by decide : (4 : ℕ) ≠ 0))
  have hq_d : q ∣ d := by
    have : q ∣ d ^ x := by
      have h := Int.natAbs_dvd_natAbs.mpr hq_dx
      simpa [Int.natAbs_pow, Int.natAbs_natCast] using h
    exact Nat.Prime.dvd_of_dvd_pow hq this
  have : q ∣ Nat.gcd b.natAbs d := Nat.dvd_gcd qb hq_d
  have hbdN : Nat.gcd b.natAbs d = 1 := by simpa [Int.gcd] using hbd
  rw [hbdN] at this
  exact hq.not_dvd_one this

theorem gcd_c_d_eq_one {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd : 0 < d) (hx : 0 < x) (hp : 0 < p) (hbd : Int.gcd b (d : ℤ) = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) : Int.gcd c (d : ℤ) = 1 := by
  change Nat.gcd c.natAbs d = 1
  by_contra hg
  have hne : Nat.gcd c.natAbs d ≠ 0 := by
    intro h0
    exact (ne_of_gt hd) (Nat.gcd_eq_zero_iff.mp h0).2
  have hgpos : 0 < Nat.gcd c.natAbs d := Nat.pos_of_ne_zero hne
  have hgt : 1 < Nat.gcd c.natAbs d :=
    lt_of_le_of_ne (Nat.succ_le_of_lt hgpos) (Ne.symm hg)
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  have qc : q ∣ c.natAbs := hqg.trans (Nat.gcd_dvd_left _ _)
  have qd : q ∣ d := hqg.trans (Nat.gcd_dvd_right _ _)
  have qcZ : (q : ℤ) ∣ c := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr qc)
  have qdZ : (q : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr qd
  have hq_b4 : (q : ℤ) ∣ b ^ 4 := by
    have : b ^ 4 = c ^ p - (d : ℤ) ^ x := by linear_combination eqn
    rw [this]
    exact dvd_sub (dvd_pow qcZ hp.ne') (dvd_pow qdZ hx.ne')
  have hq_b : q ∣ b.natAbs := by
    have : q ∣ b.natAbs ^ 4 := by
      have h := Int.natAbs_dvd_natAbs.mpr hq_b4
      simpa [Int.natAbs_pow] using h
    exact Nat.Prime.dvd_of_dvd_pow hq this
  have : q ∣ Nat.gcd b.natAbs d := Nat.dvd_gcd hq_b qd
  have hbdN : Nat.gcd b.natAbs d = 1 := by simpa [Int.gcd] using hbd
  rw [hbdN] at this
  exact hq.not_dvd_one this




/-! ## Ideal-theoretic conjugate coprimality and perfect powers -/

theorem intCast_pow (n : ℤ) (k : ℕ) :
    (⟨n, 0⟩ : OmegaRing D) ^ k = ⟨n ^ k, 0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih]
    refine OmegaRing.ext ?_ ?_
    · simp [mul_re]; ring
    · simp [mul_im]

theorem gamma_mul_conjugate_eq {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hD : 4 * D = (d : ℤ) + 1) (hx : x % 2 = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b) *
        conjugate (ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)) =
      ⟨c ^ p, 0⟩ := by
  have hN := gamma_norm_is_pth_power (d := d) (D := D) hD hx eqn
  simp [mul_conjugate_eq_qnorm, qnorm, toElement_ofElement, hN]

theorem a_sq_mul_d {d : ℕ} {x : ℕ} (hx : x % 2 = 1) :
    ((d : ℤ) ^ ((x - 1) / 2)) ^ 2 * (d : ℤ) = (d : ℤ) ^ x := by
  have hx' : 2 * ((x - 1) / 2) + 1 = x := by omega
  have hmul : ((d : ℤ) ^ ((x - 1) / 2)) ^ 2 = (d : ℤ) ^ (2 * ((x - 1) / 2)) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hmul, mul_comm, ← pow_succ', hx']

theorem gcd_c_four_dx {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hd : 0 < d) (hx : 0 < x) (hp : 0 < p) (hbd : Int.gcd b (d : ℤ) = 1)
    (hc2 : c % 2 = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    Int.gcd c ((4 : ℤ) * (d : ℤ) ^ x) = 1 := by
  have hcd := gcd_c_d_eq_one hd hx hp hbd eqn
  have hc_odd : Nat.Coprime c.natAbs 2 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
    have : Odd c := Int.odd_iff.mpr hc2
    have : c.natAbs % 2 = 1 := Nat.odd_iff.mp (Int.natAbs_odd.mpr this)
    simp [this]
  have hcdN : Nat.Coprime c.natAbs d := by simpa [Int.gcd] using hcd
  have h4 : Nat.Coprime c.natAbs 4 := by
    change Nat.Coprime _ (2 * 2); exact hc_odd.mul_right hc_odd
  have hdx : Nat.Coprime c.natAbs (d ^ x) := hcdN.pow_right _
  have hcop : Nat.Coprime c.natAbs (4 * d ^ x) := h4.mul_right hdx
  simpa [Int.gcd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using hcop

theorem conjugate_ideals_coprime {d : ℕ} {b c : ℤ} {x p : ℕ}
    [IsDomain (OmegaRing D)] [IsDedekindDomain (OmegaRing D)]
    (hD : 4 * D = (d : ℤ) + 1)
    (hd : 0 < d) (hx : x % 2 = 1) (hp : 0 < p)
    (hbd : Int.gcd b (d : ℤ) = 1) (hc2 : c % 2 = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    IsCoprime
      (Ideal.span ({ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)} :
        Set (OmegaRing D)))
      (Ideal.span ({conjugate
        (ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b))} :
        Set (OmegaRing D))) := by
  set a := (d : ℤ) ^ ((x - 1) / 2)
  set γ : OmegaRing D := ofElement (gammaOf a b)
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hne
  haveI : M.IsPrime := Ideal.IsMaximal.isPrime hMmax
  have hγ : γ ∈ M :=
    (le_trans le_sup_left hMle) (Ideal.mem_span_singleton_self _)
  have hγb : conjugate γ ∈ M :=
    (le_trans le_sup_right hMle) (Ideal.mem_span_singleton_self _)
  have hcp : ⟨c ^ p, 0⟩ ∈ M := by
    have hmul : γ * conjugate γ ∈ M * M := Ideal.mul_mem_mul hγ hγb
    have : γ * conjugate γ ∈ M := Ideal.mul_le_left hmul
    rwa [gamma_mul_conjugate_eq (D := D) hD hx eqn] at this
  have h4ad : (⟨(4 : ℤ) * a ^ 2 * (d : ℤ), 0⟩ : OmegaRing D) ∈ M := by
    have hsub : γ - conjugate γ ∈ M := sub_mem hγ hγb
    have hsq : (γ - conjugate γ) ^ 2 ∈ M :=
      Ideal.mul_le_left (by simpa [pow_two] using Ideal.mul_mem_mul hsub hsub)
    have hneg : (⟨(- (4 : ℤ) * a ^ 2 * (d : ℤ)), 0⟩ : OmegaRing D) ∈ M := by
      rwa [gamma_sub_conjugate_sq (D := D) (d := d) hD a b] at hsq
    have heq : (-⟨(- (4 : ℤ) * a ^ 2 * (d : ℤ)), 0⟩ : OmegaRing D) =
        ⟨(4 : ℤ) * a ^ 2 * (d : ℤ), 0⟩ := by
      refine OmegaRing.ext (by simp) (by simp)
    have hneg' : -⟨(- (4 : ℤ) * a ^ 2 * (d : ℤ)), 0⟩ ∈ M := neg_mem hneg
    rwa [heq] at hneg'
  have h4dx : (⟨(4 : ℤ) * (d : ℤ) ^ x, 0⟩ : OmegaRing D) ∈ M := by
    have heq :
        (⟨(4 : ℤ) * a ^ 2 * (d : ℤ), 0⟩ : OmegaRing D) =
          ⟨(4 : ℤ) * (d : ℤ) ^ x, 0⟩ := by
      refine OmegaRing.ext ?_ rfl
      show (4 : ℤ) * a ^ 2 * (d : ℤ) = 4 * (d : ℤ) ^ x
      dsimp [a]
      have h := a_sq_mul_d (d := d) hx
      calc (4 : ℤ) * ((d : ℤ) ^ ((x - 1) / 2)) ^ 2 * (d : ℤ)
          = 4 * (((d : ℤ) ^ ((x - 1) / 2)) ^ 2 * (d : ℤ)) := by ring
        _ = 4 * (d : ℤ) ^ x := by rw [h]
    rwa [← heq]
  have hcop : Int.gcd (c ^ p) ((4 : ℤ) * (d : ℤ) ^ x) = 1 := by
    have h1 := gcd_c_four_dx hd (Nat.pos_of_ne_zero (by omega : x ≠ 0)) hp hbd hc2 eqn
    have : Nat.gcd (c.natAbs ^ p) (4 * d ^ x) = 1 :=
      Nat.Coprime.pow_left p (by simpa [Int.gcd, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_natCast] using h1)
    simpa [Int.gcd, Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using this
  have hab := Int.gcd_eq_gcd_ab (c ^ p) ((4 : ℤ) * (d : ℤ) ^ x)
  rw [hcop, Nat.cast_one] at hab
  have hone : (1 : OmegaRing D) =
      ⟨c ^ p, 0⟩ * ⟨Int.gcdA (c ^ p) ((4 : ℤ) * (d : ℤ) ^ x), 0⟩ +
        ⟨(4 : ℤ) * (d : ℤ) ^ x, 0⟩ *
          ⟨Int.gcdB (c ^ p) ((4 : ℤ) * (d : ℤ) ^ x), 0⟩ := by
    apply OmegaRing.ext
    · simp [mul_re, mul_im, add_re, add_im]
      linarith [hab]
    · simp [mul_re, mul_im, add_re, add_im]
  have : (1 : OmegaRing D) ∈ M := by
    rw [hone]
    exact add_mem (Ideal.mul_mem_right _ _ hcp) (Ideal.mul_mem_right _ _ h4dx)
  exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)



theorem span_gamma_mul_conjugate_eq_c_pow {d : ℕ} {b c : ℤ} {x p : ℕ}
    (hD : 4 * D = (d : ℤ) + 1) (hx : x % 2 = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    Ideal.span ({ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)} :
        Set (OmegaRing D)) *
      Ideal.span ({conjugate
        (ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b))} :
        Set (OmegaRing D)) =
      Ideal.span ({(⟨c, 0⟩ : OmegaRing D)} : Set (OmegaRing D)) ^ p := by
  set γ : OmegaRing D := ofElement (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)
  have hnorm : γ * conjugate γ = ⟨c ^ p, 0⟩ :=
    gamma_mul_conjugate_eq (D := D) hD hx eqn
  calc
    Ideal.span {γ} * Ideal.span {conjugate γ}
        = Ideal.span ({⟨c ^ p, 0⟩} : Set (OmegaRing D)) := by
          rw [Ideal.span_singleton_mul_span_singleton, hnorm]
    _ = Ideal.span ({(⟨c, 0⟩ : OmegaRing D) ^ p} : Set (OmegaRing D)) := by
          rw [intCast_pow]
    _ = Ideal.span ({(⟨c, 0⟩ : OmegaRing D)} : Set (OmegaRing D)) ^ p :=
          (Ideal.span_singleton_pow _ _).symm

theorem gamma_is_perfect_power {d : ℕ} {b c : ℤ} {x p : ℕ}
    [IsDedekindDomain (OmegaRing D)]
    (hD : 4 * D = (d : ℤ) + 1)
    (hd : 0 < d) (hx : x % 2 = 1) (hp : 0 < p)
    (hbd : Int.gcd b (d : ℤ) = 1) (hc2 : c % 2 = 1)
    (eqn : (d : ℤ) ^ x + b ^ 4 = c ^ p) :
    ∃ I : Ideal (OmegaRing D),
      I ^ p =
        Ideal.span ({ofElement (D := D) (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)} :
          Set (OmegaRing D)) := by
  set γ : OmegaRing D := ofElement (gammaOf ((d : ℤ) ^ ((x - 1) / 2)) b)
  set A := Ideal.span ({γ} : Set (OmegaRing D))
  set B := Ideal.span ({conjugate γ} : Set (OmegaRing D))
  set C := Ideal.span ({(⟨c, 0⟩ : OmegaRing D)} : Set (OmegaRing D))
  have hcop : IsCoprime A B := by
    simpa [A, B, γ] using
      conjugate_ideals_coprime (D := D) (d := d) (b := b) (c := c) (x := x) (p := p)
        hD hd hx hp hbd hc2 eqn
  have hgcd : IsUnit (gcd A B) := by
    have h1 : gcd A B = 1 := (Ideal.isCoprime_iff_gcd).mp hcop
    simp [h1]
  have hmul : A * B = C ^ p := by
    simpa [A, B, C, γ] using
      span_gamma_mul_conjugate_eq_c_pow (D := D) (d := d) (b := b) (c := c)
        (x := x) (p := p) hD hx eqn
  obtain ⟨I, hI⟩ := exists_associated_pow_of_mul_eq_pow hgcd hmul
  exact ⟨I, (associated_iff_eq.mp hI).trans (by simp [A, γ])⟩

theorem gamma_perfect_power_167
    (b c : ℤ) (x : ℕ) (hx : x % 2 = 1)
    (hbd : Int.gcd b (167 : ℤ) = 1)
    (eqn : (167 : ℤ) ^ x + b ^ 4 = c ^ 11) :
    ∃ I : Ideal (OmegaRing 42),
      I ^ 11 =
        Ideal.span
          ({ofElement (D := 42) (gammaOf ((167 : ℤ) ^ ((x - 1) / 2)) b)} :
            Set (OmegaRing 42)) := by
  have hD : (4 : ℤ) * 42 = (167 : ℤ) + 1 := by decide
  have hd : 0 < 167 := by decide
  have hp : 0 < 11 := by decide
  have hd16 : 167 % 16 = 7 := by decide
  have hp4 : 4 ≤ 11 := by decide
  have hodd : Odd 11 := by decide
  have hc2 : c % 2 = 1 :=
    right_base_odd_of_eqn (d := 167) hd16 hx hp4 hodd hd eqn
  exact gamma_is_perfect_power (D := 42) hD hd hx hp hbd hc2 eqn

set_option maxRecDepth 2048 in
theorem gamma_perfect_power_2471
    (b c : ℤ) (x : ℕ) (hx : x % 2 = 1)
    (hbd : Int.gcd b (2471 : ℤ) = 1)
    (eqn : (2471 : ℤ) ^ x + b ^ 4 = c ^ 31) :
    ∃ I : Ideal (OmegaRing 618),
      I ^ 31 =
        Ideal.span
          ({ofElement (D := 618) (gammaOf ((2471 : ℤ) ^ ((x - 1) / 2)) b)} :
            Set (OmegaRing 618)) := by
  have hD : (4 : ℤ) * 618 = (2471 : ℤ) + 1 := by native_decide
  have hd : 0 < 2471 := by omega
  have hp : 0 < 31 := by omega
  have hd16 : 2471 % 16 = 7 := by native_decide
  have hp4 : 4 ≤ 31 := by omega
  have hodd : Odd 31 := ⟨15, by omega⟩
  have hc2 : c % 2 = 1 :=
    right_base_odd_of_eqn (d := 2471) hd16 hx hp4 hodd hd eqn
  haveI : IsDedekindDomain (OmegaRing 618) :=
    Beal.OmegaRingDedekind.instIsDedekindDomain_618
  exact gamma_is_perfect_power (D := 618) hD hd hx hp hbd hc2 eqn



/-! ## IdealAPI-shaped specializations (DedekindGap.gamma_perfect_power) -/

/-- `DedekindGap.gamma_perfect_power` for `idealAPI167`. -/
theorem gamma_perfect_power_idealAPI167
    (b c : ℤ) (x : ℕ) (hx : x % 2 = 1)
    (hbd : Int.gcd b (167 : ℤ) = 1)
    (eqn : (167 : ℤ) ^ x + b ^ 4 = c ^ 11) :
    ∃ I : idealAPI167.Ideal,
      idealAPI167.powI I 11 =
        idealAPI167.principal (gammaOf ((167 : ℤ) ^ ((x - 1) / 2)) b) :=
  gamma_perfect_power_167 b c x hx hbd eqn

set_option maxRecDepth 4096 in
/-- `DedekindGap.gamma_perfect_power` for `idealAPI2471`. -/
theorem gamma_perfect_power_idealAPI2471
    (b c : ℤ) (x : ℕ) (hx : x % 2 = 1)
    (hbd : Int.gcd b (2471 : ℤ) = 1)
    (eqn : (2471 : ℤ) ^ x + b ^ 4 = c ^ 31) :
    ∃ I : idealAPI2471.Ideal,
      idealAPI2471.powI I 31 =
        idealAPI2471.principal (gammaOf ((2471 : ℤ) ^ ((x - 1) / 2)) b) :=
  gamma_perfect_power_2471 b c x hx hbd eqn

end Beal.OmegaRingGamma

#print axioms Beal.OmegaRingGamma.conjugate_ideals_coprime
#print axioms Beal.OmegaRingGamma.gamma_is_perfect_power
#print axioms Beal.OmegaRingGamma.gamma_perfect_power_167
#print axioms Beal.OmegaRingGamma.gamma_perfect_power_2471
#print axioms Beal.OmegaRingGamma.gamma_perfect_power_idealAPI167
#print axioms Beal.OmegaRingGamma.gamma_perfect_power_idealAPI2471
