import OmegaRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic

/-!
# L2b: `IsDedekindDomain (OmegaRing D)` for D = 42 and D = 618

For squarefree `d ≡ 3 (mod 4)` with `4D = d + 1`, the monogenic order
`OmegaRing D ≅ ℤ[ω]` (`ω = (1+√-d)/2`) is the ring of integers of
`K = ℚ(√-d)`, hence a Dedekind domain.
-/

open Polynomial AdjoinRoot
open Algebra (norm)
open Beal
open OmegaRing

namespace Beal.OmegaRingDedekind

theorem four_mul_d_y_sq {d : ℕ} {x y : ℚ} {m n : ℤ}
    (hm : (m : ℚ) = 2 * x) (hn : (n : ℚ) = x ^ 2 + (d : ℚ) * y ^ 2) :
    (4 : ℚ) * d * y ^ 2 = ((4 * n - m ^ 2 : ℤ) : ℚ) := by
  have hx : x = (m : ℚ) / 2 := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    apply (eq_div_iff_mul_eq h2).mpr
    rw [mul_comm]; exact hm.symm
  have h : ((m : ℚ) / 2) ^ 2 + (d : ℚ) * y ^ 2 = n := by
    rw [← hx]; exact hn.symm
  have key : (m : ℚ) ^ 2 + (4 : ℚ) * d * y ^ 2 = 4 * n := by
    have h4 := congrArg (fun t : ℚ => 4 * t) h
    -- 4 * ((m/2)^2 + d y^2) = 4 n
    convert h4 using 1
    field_simp
    ring
  calc
    (4 : ℚ) * d * y ^ 2 = 4 * n - (m : ℚ) ^ 2 := by linear_combination key
    _ = ((4 * n - m ^ 2 : ℤ) : ℚ) := by
        simp [Int.cast_sub, Int.cast_mul, Int.cast_pow, pow_two]

theorem den_sq_dvd_four_mul {d : ℕ} {y : ℚ} {m n : ℤ}
    (hy2 : (4 : ℚ) * d * y ^ 2 = ((4 * n - m ^ 2 : ℤ) : ℚ)) :
    y.den ^ 2 ∣ 4 * d := by
  have hden0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
  have h1 : (4 : ℚ) * d * ((y.num : ℚ) / y.den) ^ 2 = (4 * n - m ^ 2 : ℤ) := by
    rwa [y.num_div_den]
  have hcleared : (4 : ℚ) * d * (y.num : ℚ) ^ 2 =
      (y.den : ℚ) ^ 2 * ((4 * n - m ^ 2 : ℤ) : ℚ) := by
    field_simp at h1 ⊢
    linear_combination h1
  have hint : ((4 * d : ℕ) : ℤ) * y.num ^ 2 =
      (y.den : ℤ) ^ 2 * (4 * n - m ^ 2) := by
    have hL : ((((4 * d : ℕ) : ℤ) * y.num ^ 2 : ℤ) : ℚ) =
        (4 : ℚ) * d * (y.num : ℚ) ^ 2 := by
      push_cast
      ring
    have hR : ((((y.den : ℤ) ^ 2 * (4 * n - m ^ 2) : ℤ) : ℚ)) =
        (y.den : ℚ) ^ 2 * ((4 * n - m ^ 2 : ℤ) : ℚ) := by
      simp [Int.cast_mul, Int.cast_pow, pow_two]
    have h' : ((((4 * d : ℕ) : ℤ) * y.num ^ 2 : ℤ) : ℚ) =
        ((((y.den : ℤ) ^ 2 * (4 * n - m ^ 2) : ℤ) : ℚ)) := by
      rw [hL, hR, hcleared]
    exact_mod_cast h'
  have hdiv : (y.den : ℤ) ^ 2 ∣ y.num ^ 2 * ((4 * d : ℕ) : ℤ) := by
    refine ⟨4 * n - m ^ 2, ?_⟩
    rw [mul_comm (y.num ^ 2)]
    exact hint
  have hcop : IsCoprime (y.num ^ 2) ((y.den : ℤ) ^ 2) := by
    have hc : IsCoprime y.num (y.den : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using y.reduced)
    exact hc.pow
  have hdiv' : (y.den : ℤ) ^ 2 ∣ ((4 * d : ℕ) : ℤ) :=
    IsCoprime.dvd_of_dvd_mul_left hcop.symm hdiv
  exact_mod_cast hdiv'

theorem den_dvd_two_of_sq_dvd {d den : ℕ}
    (hd : Squarefree d) (hodd : Odd d) (hden0 : den ≠ 0) (hdiv : den ^ 2 ∣ 4 * d) :
    den ∣ 2 := by
  have hcop : Nat.Coprime (den ^ 2) d := by
    refine Nat.coprime_of_dvd fun p hp hpden hpd => ?_
    have hp_den : p ∣ den := Nat.Prime.dvd_of_dvd_pow hp hpden
    have hp2_div : p ^ 2 ∣ 4 * d :=
      dvd_trans (pow_dvd_pow_of_dvd hp_den 2) hdiv
    by_cases h2 : p = 2
    · subst h2
      have : ¬Even d := Nat.not_even_iff.mpr (Nat.odd_iff.mp hodd)
      exact this (even_iff_two_dvd.mpr hpd)
    · have hcop4 : Nat.Coprime (p ^ 2) 4 := by
        rw [Nat.coprime_pow_left_iff (by decide : 0 < 2)]
        change Nat.Coprime p (2 ^ 2)
        rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
        exact (Nat.coprime_primes hp Nat.prime_two).2 h2
      have hp2d : p ^ 2 ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hcop4 hp2_div
      exact (Nat.squarefree_iff_prime_squarefree.mp hd) p hp (pow_two p ▸ hp2d)
  have hdiv4 : den ^ 2 ∣ 4 := Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv
  have hle : den ^ 2 ≤ 4 := Nat.le_of_dvd (by decide) hdiv4
  match den with
  | 0 => exact (hden0 rfl).elim
  | 1 => exact one_dvd _
  | 2 => exact dvd_refl _
  | n + 3 =>
    have h9 : 3 ^ 2 ≤ (n + 3) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_add_left 3 n) 2
    change (n + 3) ^ 2 ≤ 4 at hle
    change 9 ≤ (n + 3) ^ 2 at h9
    omega

theorem two_mul_im_mem_int {d : ℕ} {x y : ℚ}
    (hd : Squarefree d) (hodd : Odd d)
    (htr : ∃ m : ℤ, (m : ℚ) = 2 * x)
    (hn : ∃ n : ℤ, (n : ℚ) = x ^ 2 + (d : ℚ) * y ^ 2) :
    ∃ v : ℤ, (v : ℚ) = 2 * y := by
  obtain ⟨m, hm⟩ := htr
  obtain ⟨n, hn⟩ := hn
  have hy2 := four_mul_d_y_sq hm hn
  have hdiv := den_sq_dvd_four_mul (y := y) (m := m) (n := n) hy2
  have hden := den_dvd_two_of_sq_dvd hd hodd y.den_nz hdiv
  obtain ⟨t, ht⟩ := hden
  refine ⟨y.num * (t : ℤ), ?_⟩
  have hdz : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
  have htQ : (2 : ℚ) = y.den * t := by exact_mod_cast ht
  calc
    ((y.num * (t : ℤ) : ℤ) : ℚ) = (y.num : ℚ) * t := by simp
    _ = (y.num : ℚ) * (2 / y.den) := by
        have : (t : ℚ) = 2 / y.den := by
          apply (eq_div_iff hdz).mpr
          linear_combination -htQ
        rw [this]
    _ = 2 * ((y.num : ℚ) / y.den) := by ring
    _ = 2 * y := by rw [y.num_div_den]


private theorem helper_sq (r : ℤ) (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) :
    r * r % 4 = 0 ∨ r * r % 4 = 1 := by
  rcases hr with h | h | h | h <;> subst h <;> decide

theorem Int.sq_mod_four_eq (n : ℤ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have h : n ^ 2 % 4 = (n % 4) * (n % 4) % 4 := by
    rw [pow_two, Int.mul_emod]
  rw [h]
  exact helper_sq _ hn

theorem Int.even_of_sq_mod_four_eq_zero {n : ℤ} (h : n ^ 2 % 4 = 0) : Even n := by
  rw [Int.even_iff]
  have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hsq : (n % 4) * (n % 4) % 4 = 0 := by
    have : n ^ 2 % 4 = (n % 4) * (n % 4) % 4 := by rw [pow_two, Int.mul_emod]
    rwa [← this]
  rcases hn with h0 | h1 | h2 | h3
  · omega
  · rw [h1] at hsq; exact absurd hsq (by decide : ¬((1:ℤ) * 1 % 4 = 0))
  · omega
  · rw [h3] at hsq; exact absurd hsq (by decide : ¬((3:ℤ) * 3 % 4 = 0))

theorem Int.odd_of_sq_mod_four_eq_one {n : ℤ} (h : n ^ 2 % 4 = 1) : Odd n := by
  rw [Int.odd_iff]
  have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hsq : (n % 4) * (n % 4) % 4 = 1 := by
    have : n ^ 2 % 4 = (n % 4) * (n % 4) % 4 := by rw [pow_two, Int.mul_emod]
    rwa [← this]
  rcases hn with h0 | h1 | h2 | h3
  · rw [h0] at hsq; exact absurd hsq (by decide : ¬((0:ℤ) * 0 % 4 = 1))
  · omega
  · rw [h2] at hsq; exact absurd hsq (by decide : ¬((2:ℤ) * 2 % 4 = 1))
  · omega

theorem same_parity_of_norm_mod_four {d : ℕ} {u v : ℤ}
    (hmod : d % 4 = 3)
    (hN : (u ^ 2 + (d : ℤ) * v ^ 2) % 4 = 0) :
    Even u ∧ Even v ∨ Odd u ∧ Odd v := by
  have hu := Int.sq_mod_four_eq u
  have hv := Int.sq_mod_four_eq v
  have hd : (d : ℤ) % 4 = 3 := by exact_mod_cast hmod
  have hsum :
      (u ^ 2 % 4 + (d : ℤ) % 4 * (v ^ 2 % 4) % 4) % 4 = 0 := by
    have : (u ^ 2 + (d : ℤ) * v ^ 2) % 4 =
        (u ^ 2 % 4 + ((d : ℤ) % 4) * (v ^ 2 % 4) % 4) % 4 := by
      rw [Int.add_emod, Int.mul_emod]
    rwa [← this]
  rw [hd] at hsum
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · left; exact ⟨Int.even_of_sq_mod_four_eq_zero hu, Int.even_of_sq_mod_four_eq_zero hv⟩
  · rw [hu, hv] at hsum; exact absurd hsum (by decide)
  · rw [hu, hv] at hsum; exact absurd hsum (by decide)
  · right; exact ⟨Int.odd_of_sq_mod_four_eq_one hu, Int.odd_of_sq_mod_four_eq_one hv⟩




noncomputable def quadPoly (d : ℕ) : ℚ[X] := X ^ 2 + C (d : ℚ)
theorem irreducible_quadPoly {d : ℕ} (hd : 0 < d) : Irreducible (quadPoly d) := by
  have hform : quadPoly d = X ^ 2 - C ((-(d : ℤ) : ℚ)) := by simp [quadPoly, sub_eq_add_neg]
  rw [hform]; refine X_pow_sub_C_irreducible_of_prime Nat.prime_two ?_
  intro b hb
  have : (b ^ 2 : ℚ) < 0 := by
    rw [hb]; exact_mod_cast (neg_neg_of_pos (Int.natCast_pos.mpr hd))
  exact (not_lt.mpr (sq_nonneg b)) this
abbrev QuadField (d : ℕ) := AdjoinRoot (quadPoly d)
variable (d : ℕ) [Fact (0 < d)]
instance : Fact (Irreducible (quadPoly d)) := ⟨irreducible_quadPoly Fact.out⟩
noncomputable def theta : QuadField d := root (quadPoly d)
theorem theta_sq_int : (theta d) ^ 2 = algebraMap ℤ (QuadField d) (-(d : ℤ)) := by
  have h0 : aeval (theta d) (quadPoly d) = 0 := by simp [theta, aeval_eq, mk_self]
  simp only [quadPoly, map_add, map_pow, aeval_X, aeval_C] at h0
  have : (theta d) ^ 2 = -algebraMap ℚ (QuadField d) (d : ℚ) :=
    eq_neg_of_add_eq_zero_left h0
  rw [this, map_neg, eq_intCast]; simp
noncomputable def omega : QuadField d := (1 + theta d) / 2

theorem sq_one_add_div_two_sub_self {K : Type*} [Field K] [CharZero K]
    {x : K} {Δ : ℤ} (hx : x ^ 2 = algebraMap ℤ K Δ) (hΔ : Δ % 4 = 1) :
    ((1 + x) / 2) ^ 2 - (1 + x) / 2 = algebraMap ℤ K (Δ / 4) := by
  have he : Δ = 4 * (Δ / 4) + 1 := by omega
  have heK : (Δ : K) = 4 * ((Δ / 4 : ℤ) : K) + 1 := by exact_mod_cast he
  have hx' : x ^ 2 = (Δ : K) := by rw [hx]; simp [eq_intCast]
  calc
    ((1 + x) / 2) ^ 2 - (1 + x) / 2
        = ((1 + x) ^ 2 - 2 * (1 + x)) / 4 := by field_simp; ring
    _ = (x ^ 2 - 1) / 4 := by ring
    _ = ((Δ : K) - 1) / 4 := by rw [hx']
    _ = (4 * ((Δ / 4 : ℤ) : K) + 1 - 1) / 4 := by rw [heK]
    _ = ((Δ / 4 : ℤ) : K) := by field_simp
    _ = algebraMap ℤ K (Δ / 4) := by simp [eq_intCast]

theorem omega_sq (D : ℤ) (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) :
    (omega d) ^ 2 = omega d - algebraMap ℤ (QuadField d) D := by
  set Δ : ℤ := -(d : ℤ)
  have hΔmod : Δ % 4 = 1 := by
    have : (d : ℤ) % 4 = 3 := by exact_mod_cast hmod
    change (-(d : ℤ)) % 4 = 1; omega
  have hD4 : Δ / 4 = -D := by
    have : Δ = 4 * (Δ / 4) + 1 := by omega
    omega
  have hrel : (omega d) ^ 2 - omega d = algebraMap ℤ (QuadField d) (Δ / 4) := by
    simpa [omega] using sq_one_add_div_two_sub_self (theta_sq_int d) hΔmod
  rw [hD4, map_neg] at hrel
  rw [sub_eq_iff_eq_add] at hrel
  rw [hrel]; abel

variable {D : ℤ}

theorem omega_sq' (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) :
    (omega d) ^ 2 = omega d - (D : ℚ) • (1 : QuadField d) := by
  have h := omega_sq d D hD hmod
  convert h using 1
  simp [Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply ℤ ℚ (QuadField d)]

noncomputable def toQuadField (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) :
    OmegaRing D →+* QuadField d where
  toFun x := (x.re : ℚ) • (1 : QuadField d) + (x.im : ℚ) • omega d
  map_one' := by simp [one_re, one_im]
  map_zero' := by simp [zero_re, zero_im]
  map_add' x y := by
    simp only [add_re, add_im, Int.cast_add]
    module
  map_mul' x y := by
    have hω := omega_sq' d hD hmod
    -- Expand RHS
    have hexpand :
        ((x.re : ℚ) • (1 : QuadField d) + (x.im : ℚ) • omega d) *
          ((y.re : ℚ) • 1 + (y.im : ℚ) • omega d) =
        ((x.re * y.re : ℚ) • (1 : QuadField d)) +
          ((x.re * y.im + x.im * y.re : ℚ) • omega d) +
          ((x.im * y.im : ℚ) • (omega d) ^ 2) := by
      simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, smul_add, pow_two]
      module
    rw [hexpand, hω]
    -- (im*im) • (ω - D•1) = (im*im)•ω - (im*im*D)•1
    simp only [smul_sub, smul_smul]
    -- LHS: (re*re - D*im*im)•1 + (re*im + im*re + im*im)•ω
    -- Target after expansion: (re*re)•1 + (re*im+im*re)•ω + (im*im)•ω - (im*im*D)•1
    -- = (re*re - D*im*im)•1 + (re*im+im*re+im*im)•ω
    simp only [mul_re, mul_im, Int.cast_sub, Int.cast_add, Int.cast_mul]
    module

/-! ## Coordinates, trace, norm -/

theorem monic_quadPoly (d : ℕ) : (quadPoly d).Monic :=
  monic_X_pow_add_C (d : ℚ) (by decide : (2 : ℕ) ≠ 0)

theorem natDegree_quadPoly (d : ℕ) : (quadPoly d).natDegree = 2 := by
  change (X ^ 2 + C (d : ℚ)).natDegree = 2
  exact natDegree_X_pow_add_C

noncomputable def pb : PowerBasis ℚ (QuadField d) := powerBasis' (monic_quadPoly d)
theorem pb_gen : (pb d).gen = theta d := rfl

omit [Fact (0 < d)] in
theorem nextCoeff_quadPoly : (quadPoly d).nextCoeff = 0 := by
  have hpos : 0 < (quadPoly d).natDegree := by rw [natDegree_quadPoly d]; decide
  rw [nextCoeff_of_natDegree_pos hpos, natDegree_quadPoly d]
  change (X ^ 2 + C (d : ℚ)).coeff 1 = 0
  simp [coeff_X_pow, coeff_C]

theorem minpoly_theta : minpoly ℚ (theta d) = quadPoly d := by
  simpa [← pb_gen d] using
    (minpoly_powerBasis_gen_of_monic (f := quadPoly d) (monic_quadPoly d))

theorem finrank_quadField : Module.finrank ℚ (QuadField d) = 2 :=
  (PowerBasis.finrank (pb d)).trans (natDegree_quadPoly d)

theorem trace_theta : Algebra.trace ℚ (QuadField d) (theta d) = 0 := by
  have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly (pb d)
  rw [pb_gen d] at h
  rw [h, minpoly_theta d, nextCoeff_quadPoly d, neg_zero]

theorem exists_coords (z : QuadField d) :
    ∃ x y : ℚ, z = algebraMap ℚ (QuadField d) x +
      algebraMap ℚ (QuadField d) y * theta d := by
  let B := pb d
  have hdim : B.dim = 2 := natDegree_quadPoly d
  let e : Fin B.dim ≃ Fin 2 := (Fin.castOrderIso hdim).toEquiv
  let b2 : Basis (Fin 2) ℚ (QuadField d) := B.basis.reindex e
  have hz : z = b2.repr z 0 • b2 0 + b2.repr z 1 • b2 1 := by
    simpa [Fin.sum_univ_two] using (b2.sum_repr z).symm
  have hb0 : b2 0 = 1 := by
    dsimp [b2]
    have : e.symm 0 = ⟨0, hdim ▸ Nat.zero_lt_two⟩ := Fin.ext (by simp [e])
    rw [Basis.reindex_apply, this, PowerBasis.basis_eq_pow, pow_zero]
  have hb1 : b2 1 = theta d := by
    dsimp [b2, theta]
    have : e.symm 1 = ⟨1, hdim ▸ Nat.one_lt_two⟩ := Fin.ext (by simp [e])
    rw [Basis.reindex_apply, this, PowerBasis.basis_eq_pow, pow_one]; rfl
  refine ⟨b2.repr z 0, b2.repr z 1, ?_⟩
  convert hz using 1
  rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem trace_coord (x y : ℚ) :
    Algebra.trace ℚ (QuadField d)
      (algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d) = 2 * x := by
  have hy : algebraMap ℚ (QuadField d) y * theta d = y • theta d := (Algebra.smul_def y _).symm
  rw [map_add, hy, LinearMap.map_smul, Algebra.trace_algebraMap, finrank_quadField,
    trace_theta]
  ring_nf; simp

theorem norm_theta : norm ℚ (theta d) = (d : ℚ) := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb d)
  rw [pb_gen d, minpoly_theta d] at h
  have hdim : (pb d).dim = 2 := natDegree_quadPoly d
  rw [h, hdim]
  have : (-1 : ℚ) ^ 2 = 1 := by norm_num
  rw [this, one_mul]
  change (X ^ 2 + C (d : ℚ)).coeff 0 = (d : ℚ)
  simp [coeff_X_pow, coeff_C]

theorem theta_ne_zero : theta d ≠ 0 := by
  intro h
  have : norm ℚ (theta d) = 0 := by rw [h]; exact Algebra.norm_zero
  rw [norm_theta d] at this
  exact (Nat.cast_ne_zero.mpr (ne_of_gt (Fact.out : 0 < d))) this

theorem coords_unique {x₁ y₁ x₂ y₂ : ℚ}
    (h : algebraMap ℚ (QuadField d) x₁ + algebraMap ℚ (QuadField d) y₁ * theta d =
      algebraMap ℚ (QuadField d) x₂ + algebraMap ℚ (QuadField d) y₂ * theta d) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have htr := congrArg (Algebra.trace ℚ (QuadField d)) h
  rw [trace_coord d, trace_coord d] at htr
  have hx : x₁ = x₂ := mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) htr
  subst hx
  have hyθ : algebraMap ℚ (QuadField d) y₁ * theta d =
      algebraMap ℚ (QuadField d) y₂ * theta d := by
    have := congrArg (fun t => t - algebraMap ℚ (QuadField d) x₁) h
    simpa [add_sub_cancel_left] using this
  have : algebraMap ℚ (QuadField d) (y₁ - y₂) * theta d = 0 := by
    rw [map_sub, sub_mul, hyθ, sub_self]
  rcases mul_eq_zero.mp this with hy0 | ht0
  · exact ⟨rfl, sub_eq_zero.mp ((FaithfulSMul.algebraMap_eq_zero_iff ℚ (QuadField d)).mp hy0)⟩
  · exact absurd ht0 (theta_ne_zero d)

theorem theta_sq : (theta d) ^ 2 = -algebraMap ℚ (QuadField d) (d : ℚ) := by
  have h0 : aeval (theta d) (quadPoly d) = 0 := by simp [theta, aeval_eq, mk_self]
  simp only [quadPoly, map_add, map_pow, aeval_X, aeval_C] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem norm_coord (x y : ℚ) :
    norm ℚ (algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d) =
      x ^ 2 + (d : ℚ) * y ^ 2 := by
  have hdim : (pb d).dim = 2 := natDegree_quadPoly d
  let e : Fin (pb d).dim ≃ Fin 2 := (Fin.castOrderIso hdim).toEquiv
  let b2 : Basis (Fin 2) ℚ (QuadField d) := (pb d).basis.reindex e
  rw [Algebra.norm_eq_matrix_det b2, Matrix.det_fin_two]
  have hb0 : b2 0 = 1 := by
    dsimp [b2]
    have : e.symm 0 = ⟨0, hdim ▸ Nat.zero_lt_two⟩ := Fin.ext (by simp [e])
    rw [Basis.reindex_apply, this, PowerBasis.basis_eq_pow, pow_zero]
  have hb1 : b2 1 = theta d := by
    dsimp [b2]
    have : e.symm 1 = ⟨1, hdim ▸ Nat.one_lt_two⟩ := Fin.ext (by simp [e])
    rw [Basis.reindex_apply, this, PowerBasis.basis_eq_pow, pow_one, pb_gen]
  set z := algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d
  have hz0 : z * b2 0 = x • b2 0 + y • b2 1 := by
    dsimp [z]; rw [hb0, hb1, mul_one]; simp only [Algebra.smul_def, mul_one]; abel
  have hz1 : z * b2 1 = (-(d : ℚ) * y) • b2 0 + x • b2 1 := by
    dsimp [z]; rw [hb0, hb1]
    have hθ := theta_sq d
    have hcalc :
        (algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d) * theta d
          = (-(d : ℚ) * y) • (1 : QuadField d) + x • theta d := by
      calc
        _ = algebraMap ℚ (QuadField d) x * theta d +
              algebraMap ℚ (QuadField d) y * (theta d) ^ 2 := by ring
        _ = algebraMap ℚ (QuadField d) x * theta d +
              algebraMap ℚ (QuadField d) y * (-algebraMap ℚ (QuadField d) (d : ℚ)) := by rw [hθ]
        _ = (-(d : ℚ) * y) • (1 : QuadField d) + x • theta d := by
              simp only [Algebra.smul_def, mul_one, map_mul, map_neg, mul_neg]; ring
    exact hcalc
  have M00 : Algebra.leftMulMatrix b2 z 0 0 = x := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hz0, map_add, map_smul, map_smul]
    simp [Basis.repr_self, Finsupp.single_apply]
  have M01 : Algebra.leftMulMatrix b2 z 0 1 = -(d : ℚ) * y := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hz1, map_add, map_smul, map_smul]
    simp [Basis.repr_self, Finsupp.single_apply]
  have M10 : Algebra.leftMulMatrix b2 z 1 0 = y := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hz0, map_add, map_smul, map_smul]
    simp [Basis.repr_self, Finsupp.single_apply]
  have M11 : Algebra.leftMulMatrix b2 z 1 1 = x := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hz1, map_add, map_smul, map_smul]
    simp [Basis.repr_self, Finsupp.single_apply]
  rw [M00, M01, M10, M11]; ring

theorem isIntegral_implies_trace_norm_int {x y : ℚ}
    (h : IsIntegral ℤ
      (algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d)) :
    (∃ m : ℤ, (m : ℚ) = 2 * x) ∧ (∃ n : ℤ, (n : ℚ) = x ^ 2 + (d : ℚ) * y ^ 2) := by
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := QuadField d) h
  rw [trace_coord d] at htr
  have hN := Algebra.isIntegral_norm (R := ℤ) (K := ℚ) (L := QuadField d) h
  rw [norm_coord d] at hN
  constructor
  · exact (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp htr
  · exact (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp hN

theorem charpoly_aeval (x y : ℚ) :
    (x • (1 : QuadField d) + y • theta d) ^ 2
      - (2 * x) • (x • 1 + y • theta d)
      + (x ^ 2 + (d : ℚ) * y ^ 2) • (1 : QuadField d) = 0 := by
  have hθ : (theta d) ^ 2 = (-(d : ℚ)) • (1 : QuadField d) := by
    rw [theta_sq, Algebra.algebraMap_eq_smul_one, neg_smul]
  have hexpand :
      (x • (1 : QuadField d) + y • theta d) ^ 2 =
        (x * x : ℚ) • (1 : QuadField d) + (x * y + y * x : ℚ) • theta d
          + (y * y : ℚ) • (theta d) ^ 2 := by
    simp only [pow_two, mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one]
    module
  rw [hexpand, hθ]
  simp only [smul_add, smul_smul, smul_neg, neg_smul]
  have h1 : (x * x + y * y * (-(d : ℚ)) - (2 * x) * x + (x ^ 2 + (d : ℚ) * y ^ 2) : ℚ) = 0 := by
    ring
  have h2 : (x * y + y * x - (2 * x) * y : ℚ) = 0 := by ring
  trans
    (x * x + y * y * (-(d : ℚ)) - (2 * x) * x + (x ^ 2 + (d : ℚ) * y ^ 2) : ℚ) •
        (1 : QuadField d) +
      (x * y + y * x - (2 * x) * y : ℚ) • theta d
  · module
  · rw [h1, h2]; simp

theorem smul_one_mul (r : ℚ) (z : QuadField d) :
    (r • (1 : QuadField d)) * z = r • z := by
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]

theorem isIntegral_of_trace_norm_int {x y : ℚ}
    (htr : ∃ m : ℤ, (m : ℚ) = 2 * x)
    (hn : ∃ n : ℤ, (n : ℚ) = x ^ 2 + (d : ℚ) * y ^ 2) :
    IsIntegral ℤ (x • (1 : QuadField d) + y • theta d) := by
  obtain ⟨m, hm⟩ := htr
  obtain ⟨n, hn⟩ := hn
  refine ⟨X ^ 2 - C m * X + C n, by monicity!, ?_⟩
  have h := charpoly_aeval d x y
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_X_pow]
  have hm'' : algebraMap ℤ (QuadField d) m = (2 * x) • (1 : QuadField d) := by
    have : algebraMap ℤ (QuadField d) m = algebraMap ℚ (QuadField d) (m : ℚ) :=
      (IsScalarTower.algebraMap_apply ℤ ℚ (QuadField d) m).symm
    rw [this, hm, Algebra.algebraMap_eq_smul_one]
  have hn'' : algebraMap ℤ (QuadField d) n =
      (x ^ 2 + (d : ℚ) * y ^ 2) • (1 : QuadField d) := by
    have : algebraMap ℤ (QuadField d) n = algebraMap ℚ (QuadField d) (n : ℚ) :=
      (IsScalarTower.algebraMap_apply ℤ ℚ (QuadField d) n).symm
    rw [this, hn, Algebra.algebraMap_eq_smul_one]
  rw [hm'', hn'', smul_one_mul]
  exact h

/-! ## Integral elements are ω-coordinates -/

theorem isIntegral_omega (hmod : d % 4 = 3) :
    IsIntegral ℤ (omega d) := by
  set Δ : ℤ := -(d : ℤ)
  have hΔmod : Δ % 4 = 1 := by
    have : (d : ℤ) % 4 = 3 := by exact_mod_cast hmod
    change (-(d : ℤ)) % 4 = 1; omega
  refine ⟨X ^ 2 - X - C (Δ / 4), by monicity!, ?_⟩
  have h := sq_one_add_div_two_sub_self (theta_sq_int d) hΔmod
  dsimp [omega]
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  -- goal: omega^2 - omega - algebraMap(Δ/4) = 0
  exact sub_eq_zero.mpr h

theorem odd_of_mod_four_eq_three' {n : ℕ} (h : n % 4 = 3) : Odd n :=
  ⟨n / 2, by omega⟩

theorem integral_eq_omega_coords
    (hd : Squarefree d) (hmod : d % 4 = 3) {z : QuadField d}
    (hz : IsIntegral ℤ z) :
    ∃ a b : ℤ, z = (a : ℚ) • (1 : QuadField d) + (b : ℚ) • omega d := by
  obtain ⟨x, y, hzxy⟩ := exists_coords d z
  have hz' : IsIntegral ℤ
      (algebraMap ℚ (QuadField d) x + algebraMap ℚ (QuadField d) y * theta d) := by
    rwa [← hzxy]
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := isIntegral_implies_trace_norm_int d hz'
  obtain ⟨v, hv⟩ :=
    two_mul_im_mem_int hd (odd_of_mod_four_eq_three' hmod) ⟨m, hm⟩ ⟨n, hn⟩
  have hx : x = (m : ℚ) / 2 := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    exact (eq_div_iff_mul_eq h2).mpr (by rw [mul_comm]; exact hm.symm)
  have hy : y = (v : ℚ) / 2 := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    exact (eq_div_iff_mul_eq h2).mpr (by rw [mul_comm]; exact hv.symm)
  have hN4 : (m ^ 2 + (d : ℤ) * v ^ 2) % 4 = 0 := by
    have key : ((m : ℚ) ^ 2 + (d : ℚ) * (v : ℚ) ^ 2) / 4 = n := by
      calc
        ((m : ℚ) ^ 2 + (d : ℚ) * (v : ℚ) ^ 2) / 4
            = ((m : ℚ) / 2) ^ 2 + (d : ℚ) * ((v : ℚ) / 2) ^ 2 := by ring
        _ = x ^ 2 + (d : ℚ) * y ^ 2 := by rw [← hx, ← hy]
        _ = n := hn.symm
    have h4 : (m : ℚ) ^ 2 + (d : ℚ) * (v : ℚ) ^ 2 = 4 * n := by
      have h20 : (4 : ℚ) ≠ 0 := by norm_num
      convert (div_eq_iff h20).mp key using 1
      ring
    have hint : m ^ 2 + (d : ℤ) * v ^ 2 = 4 * n := by exact_mod_cast h4
    omega
  have hpar := same_parity_of_norm_mod_four hmod hN4
  have hdiv2 : (2 : ℤ) ∣ (m - v) := by
    apply Even.two_dvd
    rw [Int.even_sub]
    rcases hpar with ⟨hm_e, hv_e⟩ | ⟨hm_o, hv_o⟩
    · exact iff_of_true hm_e hv_e
    · exact iff_of_false (Int.not_even_iff_odd.mpr hm_o) (Int.not_even_iff_odd.mpr hv_o)
  obtain ⟨a, ha⟩ := hdiv2
  refine ⟨a, v, ?_⟩
  have hm' : m = 2 * a + v := by linear_combination ha
  rw [hzxy, hx, hy, hm']
  -- Need: alg((2a+v)/2) + alg(v/2)*θ = a•1 + v•ω
  dsimp [omega]
  have key :
      algebraMap ℚ (QuadField d) (((2 * a + v : ℤ) : ℚ) / 2) +
          algebraMap ℚ (QuadField d) ((v : ℚ) / 2) * theta d =
        (a : ℚ) • (1 : QuadField d) + (v : ℚ) • ((1 + theta d) / 2) := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    -- Rewrite RHS
    simp only [Algebra.smul_def, mul_one]
    -- Clear /2 by multiplying criterion: use FaithfulSMul after bringing to common form
    -- Expand RHS: alg(a) + alg(v) * ((1+θ)/2)
    -- = alg(a) + alg(v)/2 + alg(v)/2 * θ   (if we can distribute)
    have hdist :
        algebraMap ℚ (QuadField d) (v : ℚ) * ((1 + theta d) / 2) =
          algebraMap ℚ (QuadField d) ((v : ℚ) / 2) +
            algebraMap ℚ (QuadField d) ((v : ℚ) / 2) * theta d := by
      have : (1 + theta d) / 2 = 1 / 2 + theta d / 2 := by ring
      rw [this, mul_add]
      have hv2 : algebraMap ℚ (QuadField d) (v : ℚ) * (1 / 2 : QuadField d) =
          algebraMap ℚ (QuadField d) ((v : ℚ) / 2) := by
        have : (1 / 2 : QuadField d) = algebraMap ℚ _ (1 / 2) := by simp
        rw [this, ← map_mul]; ring
      have hvθ : algebraMap ℚ (QuadField d) (v : ℚ) * (theta d / 2) =
          algebraMap ℚ (QuadField d) ((v : ℚ) / 2) * theta d := by
        have : (theta d / 2) = (algebraMap ℚ (QuadField d) (1 / 2)) * theta d := by
          simp [div_eq_mul_inv]; ring
        rw [this, ← mul_assoc, ← map_mul]
        ring
      rw [hv2, hvθ]
    rw [hdist]
    -- LHS: alg((2a+v)/2) + alg(v/2)*θ
    -- RHS: alg(a) + alg(v/2) + alg(v/2)*θ
    -- Suffices: alg((2a+v)/2) = alg(a) + alg(v/2)
    have : algebraMap ℚ (QuadField d) (((2 * a + v : ℤ) : ℚ) / 2) =
        algebraMap ℚ (QuadField d) (a : ℚ) + algebraMap ℚ (QuadField d) ((v : ℚ) / 2) := by
      rw [← map_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [this]
    abel
  exact key







theorem algebraMap_int_omegaRing (n : ℤ) :
    algebraMap ℤ (OmegaRing D) n = ⟨n, 0⟩ := rfl

/-! ## Embedding lemmas (no Algebra instance yet) -/

theorem toQuadField_int
    (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) (n : ℤ) :
    toQuadField (d := d) (D := D) hD hmod ⟨n, 0⟩ = algebraMap ℤ (QuadField d) n := by
  change ((n : ℚ) • (1 : QuadField d) + (0 : ℚ) • omega d) = algebraMap ℤ (QuadField d) n
  rw [zero_smul, add_zero]
  exact ((IsScalarTower.algebraMap_apply ℤ ℚ (QuadField d) n).trans
    (Algebra.algebraMap_eq_smul_one (n : ℚ))).symm

theorem toQuadField_coords
    (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) (x : OmegaRing D) :
    toQuadField (d := d) (D := D) hD hmod x =
      algebraMap ℚ (QuadField d) ((x.re : ℚ) + (x.im : ℚ) / 2) +
        algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) * theta d := by
  change (x.re : ℚ) • (1 : QuadField d) + (x.im : ℚ) • omega d =
    algebraMap ℚ (QuadField d) ((x.re : ℚ) + (x.im : ℚ) / 2) +
      algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) * theta d
  dsimp [omega]
  simp only [Algebra.smul_def, mul_one]
  have hdist :
      algebraMap ℚ (QuadField d) (x.im : ℚ) * ((1 + theta d) / 2) =
        algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) +
          algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) * theta d := by
    have : (1 + theta d) / 2 = (1 / 2 : QuadField d) + theta d / 2 := by ring
    rw [this, mul_add]
    have e1 : algebraMap ℚ (QuadField d) (x.im : ℚ) * (1 / 2 : QuadField d) =
        algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) := by
      have : (1 / 2 : QuadField d) = algebraMap ℚ _ (1 / 2) := by simp
      rw [this, ← map_mul]; ring
    have e2 : algebraMap ℚ (QuadField d) (x.im : ℚ) * (theta d / 2) =
        algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) * theta d := by
      have : theta d / 2 = algebraMap ℚ (QuadField d) (1 / 2) * theta d := by
        simp [div_eq_mul_inv]; ring
      rw [this, ← mul_assoc, ← map_mul]; ring
    rw [e1, e2]
  rw [hdist, ← add_assoc, ← map_add]
  congr 1

theorem toQuadField_injective
    (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) :
    Function.Injective (toQuadField (d := d) (D := D) hD hmod) := by
  intro x y h
  have h' :
      algebraMap ℚ (QuadField d) ((x.re : ℚ) + (x.im : ℚ) / 2) +
          algebraMap ℚ (QuadField d) ((x.im : ℚ) / 2) * theta d =
        algebraMap ℚ (QuadField d) ((y.re : ℚ) + (y.im : ℚ) / 2) +
          algebraMap ℚ (QuadField d) ((y.im : ℚ) / 2) * theta d := by
    simpa [toQuadField_coords d hD hmod] using h
  obtain ⟨hre, him⟩ := coords_unique d h'
  have him' : (x.im : ℚ) = (y.im : ℚ) := by
    have : (x.im : ℚ) / 2 = (y.im : ℚ) / 2 := him
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    exact (div_left_inj' h2).mp this
  have hre' : (x.re : ℚ) = (y.re : ℚ) := by
    have : (x.re : ℚ) + (x.im : ℚ) / 2 = (y.re : ℚ) + (y.im : ℚ) / 2 := hre
    linarith [him']
  ext
  · exact_mod_cast hre'
  · exact_mod_cast him'

theorem toQuadField_isIntegral
    (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) (x : OmegaRing D) :
    IsIntegral ℤ (toQuadField (d := d) (D := D) hD hmod x) := by
  have hω : IsIntegral ℤ (omega d) := isIntegral_omega d hmod
  have hre : (x.re : ℚ) • (1 : QuadField d) = algebraMap ℤ (QuadField d) x.re := by
    calc (x.re : ℚ) • (1 : QuadField d)
        = algebraMap ℚ (QuadField d) (x.re : ℚ) :=
          (Algebra.algebraMap_eq_smul_one (x.re : ℚ)).symm
      _ = algebraMap ℤ (QuadField d) x.re :=
          (IsScalarTower.algebraMap_apply ℤ ℚ (QuadField d) x.re).symm
  have him : (x.im : ℚ) • omega d = algebraMap ℤ (QuadField d) x.im * omega d := by
    calc (x.im : ℚ) • omega d
        = algebraMap ℚ (QuadField d) (x.im : ℚ) * omega d := by rw [Algebra.smul_def]
      _ = algebraMap ℤ (QuadField d) x.im * omega d := by simp [eq_intCast]
  change IsIntegral ℤ ((x.re : ℚ) • (1 : QuadField d) + (x.im : ℚ) • omega d)
  rw [hre, him]
  exact (isIntegral_algebraMap).add (isIntegral_algebraMap.mul hω)

/-- Under the half-integer ROI hypotheses, `OmegaRing D` is a Dedekind domain. -/
theorem isDedekindDomain_omegaRing
    (hD : 4 * D = (d : ℤ) + 1) (hmod : d % 4 = 3) (hd : Squarefree d)
    (hpos : (0 : ℤ) < 4 * D - 1) :
    IsDedekindDomain (OmegaRing D) := by
  letI : IsDomain (OmegaRing D) := OmegaRing.isDomain hpos
  letI : Algebra (OmegaRing D) (QuadField d) :=
    RingHom.toAlgebra (toQuadField (d := d) (D := D) hD hmod)
  letI : IsScalarTower ℤ (OmegaRing D) (QuadField d) := by
    refine IsScalarTower.of_algebraMap_eq fun n => ?_
    change algebraMap ℤ (QuadField d) n =
      algebraMap (OmegaRing D) (QuadField d) (algebraMap ℤ (OmegaRing D) n)
    rw [algebraMap_int_omegaRing]
    show algebraMap ℤ (QuadField d) n = toQuadField (d := d) (D := D) hD hmod ⟨n, 0⟩
    exact (toQuadField_int d hD hmod n).symm
  letI : IsIntegralClosure (OmegaRing D) ℤ (QuadField d) :=
    { algebraMap_injective' := toQuadField_injective d hD hmod
      isIntegral_iff := by
        intro z
        constructor
        · intro hz
          obtain ⟨a, b, hab⟩ := integral_eq_omega_coords d hd hmod hz
          refine ⟨⟨a, b⟩, ?_⟩
          change toQuadField (d := d) (D := D) hD hmod ⟨a, b⟩ = z
          simpa [toQuadField] using hab.symm
        · rintro ⟨y, rfl⟩
          change IsIntegral ℤ (toQuadField (d := d) (D := D) hD hmod y)
          exact toQuadField_isIntegral d hD hmod y }
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ (QuadField d) (OmegaRing D)

/-! ## Project bases: D = 42 (d = 167) and D = 618 (d = 2471) -/

instance fact_pos_167 : Fact (0 < 167) := ⟨by decide⟩
instance fact_pos_2471 : Fact (0 < 2471) := ⟨by decide⟩

theorem isDedekindDomain_42 : IsDedekindDomain (OmegaRing 42) := by
  refine isDedekindDomain_omegaRing (d := 167) (D := 42) (by decide)
    (by decide) Beal.IdealDescent.squarefree_167 (by decide)

theorem isDedekindDomain_618 : IsDedekindDomain (OmegaRing 618) := by
  refine isDedekindDomain_omegaRing (d := 2471) (D := 618) (by decide)
    (by decide) Beal.IdealDescent.squarefree_2471 (by decide)

instance instIsDedekindDomain_42 : IsDedekindDomain (OmegaRing 42) :=
  isDedekindDomain_42

instance instIsDedekindDomain_618 : IsDedekindDomain (OmegaRing 618) :=
  isDedekindDomain_618

end Beal.OmegaRingDedekind

#print axioms Beal.OmegaRingDedekind.isDedekindDomain_42
#print axioms Beal.OmegaRingDedekind.isDedekindDomain_618
