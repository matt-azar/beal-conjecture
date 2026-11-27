import OmegaRing
import OmegaRingDedekind
import OmegaRingEta
import OmegaRingGamma
import Mathlib.RingTheory.ClassGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Card
import Mathlib.Tactic

/-!
# L2e: `DedekindGap.principalizer`

Given an ideal `I` with `I^p` principal and the L2d ideal `P` with
`P^p = (η)` of class order `p`, some product `I P^k` is principal.

The argument uses that Mathlib's `ClassGroup (OmegaRing D)` has order equal
to the classical class number (`11` / `62`). That identification is isolated
as `ClassGroupOrderHypothesis` — the reduced-form counts in
`IdealDescent.lean` are not yet connected to `ClassGroup` (AGENTS L2e).

Everything else is derived from L2b–L2d and elementary finite abelian group
facts: `p²∤|Cl|` forces `Cl[p] = ⟨[P]⟩`, so `[I]` is a power of `[P]`.
-/

open Beal
open OmegaRing
open IdealDescent
open QuadraticBridge
open TwistIdentity
open OmegaRingEta
open Subgroup
open scoped nonZeroDivisors

namespace Beal.OmegaRingPrincipalizer

/-! ## Remaining ClassGroup hypothesis -/

/-- **L2e remaining assumption.** Mathlib's `ClassGroup R` is finite of
order `h`. For the project bases one takes `R = OmegaRing 42`, `h = 11` and
`R = OmegaRing 618`, `h = 62`, matching `reducedFormCount`, which is not yet
linked formally to `ClassGroup`. -/
structure ClassGroupOrderHypothesis (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (h : ℕ) : Prop where
  finite : Finite (ClassGroup R)
  card_eq : Nat.card (ClassGroup R) = h

/-- Named form of the hypothesis at `d = 167`. -/
abbrev classGroupOrder_167 : Prop := ClassGroupOrderHypothesis (OmegaRing 42) 11

/-- Named form of the hypothesis at `d = 2471`. -/
abbrev classGroupOrder_2471 : Prop := ClassGroupOrderHypothesis (OmegaRing 618) 62

/-! ## Finite abelian groups: `p`-torsion equals `⟨g⟩` -/

theorem card_sup_of_inf_eq_bot {G : Type*} [CommGroup G] [Finite G]
    {H K : Subgroup G} (h : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  haveI : K.Normal := inferInstance
  have hrel : K.relindex (H ⊔ K) = Nat.card H := by
    rw [relindex_sup_right, ← inf_relindex_left, h, relindex_bot_left]
  have h1 := card_mul_index (H := K)
  have h2 := card_mul_index (H := H ⊔ K)
  have h3 := relindex_mul_index (le_sup_right : K ≤ H ⊔ K)
  have hSpos : 0 < (H ⊔ K).index := by
    refine Nat.pos_of_ne_zero ?_
    intro hz
    have : Nat.card G = 0 := by simpa [hz] using h2.symm
    exact (Nat.card_pos (α := G)).ne' this
  apply Nat.mul_left_cancel hSpos
  calc
    (H ⊔ K).index * Nat.card ↥(H ⊔ K)
        = Nat.card G := by rw [mul_comm, h2]
    _ = Nat.card K * K.index := h1.symm
    _ = Nat.card K * (K.relindex (H ⊔ K) * (H ⊔ K).index) := by rw [← h3]
    _ = (H ⊔ K).index * (Nat.card H * Nat.card K) := by
      rw [hrel, mul_comm (Nat.card K), mul_assoc, mul_left_comm, mul_comm]

/-- If `g` has prime order `p` and `p² ∤ |G|`, every `x` with `x^p = 1`
lies in `⟨g⟩`. -/
theorem mem_zpowers_of_pow_eq_one {G : Type*} [CommGroup G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) {g x : G}
    (hg : orderOf g = p) (hx : x ^ p = 1) (hp2 : ¬(p * p ∣ Nat.card G)) :
    x ∈ zpowers g := by
  have hxord : orderOf x ∣ p := (orderOf_dvd_iff_pow_eq_one).mpr hx
  rcases (Nat.dvd_prime hp).mp hxord with h1 | hxp
  · rw [orderOf_eq_one_iff.mp h1]
    exact one_mem _
  · by_contra hxmem
    set H : Subgroup G := zpowers x
    set K : Subgroup G := zpowers g
    have hHcard : Nat.card H = p := by
      change Nat.card (zpowers x) = p; rw [Nat.card_zpowers, hxp]
    have hKcard : Nat.card K = p := by
      change Nat.card (zpowers g) = p; rw [Nat.card_zpowers, hg]
    have hinf : H ⊓ K = ⊥ := by
      have hdvd : Nat.card ↥(H ⊓ K) ∣ p := by
        have := card_dvd_of_le (show H ⊓ K ≤ K from inf_le_right)
        rwa [hKcard] at this
      rcases (Nat.dvd_prime hp).mp hdvd with hc1 | hcp
      · exact (eq_bot_iff_card (H ⊓ K)).2 hc1
      · have hle : Nat.card K ≤ Nat.card ↥(H ⊓ K) := by rw [hKcard, hcp]
        have heq : H ⊓ K = K := eq_of_le_of_card_ge inf_le_right hle
        have hKleH : K ≤ H := heq ▸ inf_le_left
        have hHeqK : K = H :=
          eq_of_le_of_card_ge hKleH (by simp [hHcard, hKcard])
        exact (hxmem (by rw [hHeqK]; exact mem_zpowers x)).elim
    have hsupcard : Nat.card ↥(H ⊔ K) = p * p := by
      rw [card_sup_of_inf_eq_bot hinf, hHcard, hKcard]
    exact hp2 (hsupcard ▸ card_subgroup_dvd_card (H ⊔ K))

/-- From `x ∈ ⟨g⟩` with `orderOf g = p`, choose `n < p` with `x * g^n = 1`. -/
theorem exists_nat_lt_order_mul_eq_one {G : Type*} [Group G] {p : ℕ}
    {g x : G} (hp : 0 < p) (hg : orderOf g = p) (hx : x ∈ zpowers g) :
    ∃ n : ℕ, n < p ∧ x * g ^ n = 1 := by
  obtain ⟨k, rfl⟩ := (mem_zpowers_iff).1 hx
  let r := Int.natMod k p
  have hr : r < p := Int.natMod_lt hp.ne'
  have hmod : (r : ℤ) ≡ k [ZMOD (p : ℤ)] := by
    have hnonneg : 0 ≤ k % (p : ℤ) :=
      Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hp.ne')
    dsimp [r, Int.natMod]
    rw [Int.toNat_of_nonneg hnonneg]
    exact Int.mod_modEq k p
  have hx' : g ^ (r : ℤ) = g ^ k :=
    (zpow_eq_zpow_iff_modEq).2 (by simpa [hg] using hmod)
  by_cases hr0 : r = 0
  · refine ⟨0, hp, ?_⟩
    have : g ^ k = 1 := by
      rw [← hx']
      simp [hr0]
    simp [this]
  · refine ⟨p - r, Nat.sub_lt hp (Nat.pos_of_ne_zero hr0), ?_⟩
    have hrle : r ≤ p := Nat.le_of_lt hr
    have hsum : r + (p - r) = p := Nat.add_sub_cancel' hrle
    calc
      g ^ k * g ^ (p - r)
          = g ^ r * g ^ (p - r) := by rw [← hx', zpow_natCast]
      _ = g ^ (r + (p - r)) := (pow_add _ _ _).symm
      _ = g ^ p := by rw [hsum]
      _ = 1 := by rw [← hg]; exact pow_orderOf_eq_one g

/-! ## Class of `P` has order `p` -/

theorem ideal_ne_bot_of_two_mem {D : ℤ} {I : Ideal (OmegaRing D)}
    (h : (⟨(2 : ℤ), 0⟩ : OmegaRing D) ∈ I) : I ≠ ⊥ := by
  intro hbot
  rw [hbot] at h
  have : (⟨(2 : ℤ), 0⟩ : OmegaRing D) = 0 := (Submodule.mem_bot _).1 h
  exact absurd (congrArg OmegaRing.re this) (by decide : (2 : ℤ) ≠ 0)

theorem mk0_pow_eq_one_of_principal {R : Type*} [CommRing R] [IsDomain R]
    [IsDedekindDomain R] {I : Ideal R} (hI : I ∈ (Ideal R)⁰) {n : ℕ}
    (hprin : Submodule.IsPrincipal ((⟨I, hI⟩ : (Ideal R)⁰) ^ n : Ideal R)) :
    ClassGroup.mk0 ⟨I, hI⟩ ^ n = 1 := by
  rw [← map_pow]
  exact (ClassGroup.mk0_eq_one_iff _).2 hprin

theorem order_eq_p_of_P {D : ℤ} {eta : Element} {p : ℕ} {P : Ideal (OmegaRing D)}
    [IsDomain (OmegaRing D)] [IsDedekindDomain (OmegaRing D)]
    [Fact (Nat.Prime p)]
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)))
    (h2 : (⟨(2 : ℤ), 0⟩ : OmegaRing D) ∈ P)
    (hnp : ¬ ∃ α : OmegaRing D, P = Ideal.span {α}) :
    orderOf (ClassGroup.mk0 ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr
      (ideal_ne_bot_of_two_mem h2)⟩) = p := by
  refine (orderOf_eq_prime_iff).2 ⟨?_, ?_⟩
  · exact mk0_pow_eq_one_of_principal _ ⟨ofElement (D := D) eta, hP⟩
  · intro hg1
    have : Submodule.IsPrincipal P := (ClassGroup.mk0_eq_one_iff _).1 hg1
    exact hnp ⟨Submodule.IsPrincipal.generator P,
      (Ideal.span_singleton_generator P).symm⟩

theorem pow_mem_nonZeroDivisors_ideal {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰) (n : ℕ) :
    I ^ n ∈ (Ideal R)⁰ := by
  refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
  cases n with
  | zero =>
    intro h
    rw [pow_zero, Ideal.one_eq_top] at h
    exact top_ne_bot h
  | succ n =>
    exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hI)

/-! ## Principalizer from the ClassGroup-order hypothesis -/

theorem exists_principalizer_of_classGroupOrder
    {D : ℤ} {eta : Element} {p h : ℕ} {P : Ideal (OmegaRing D)}
    [IsDomain (OmegaRing D)] [IsDedekindDomain (OmegaRing D)]
    (hh : ClassGroupOrderHypothesis (OmegaRing D) h)
    (hp : Nat.Prime p) (hp2 : ¬(p * p ∣ h))
    (hP : P ^ p = Ideal.span ({ofElement (D := D) eta} : Set (OmegaRing D)))
    (h2 : (⟨(2 : ℤ), 0⟩ : OmegaRing D) ∈ P)
    (hnp : ¬ ∃ α : OmegaRing D, P = Ideal.span {α})
    (I : Ideal (OmegaRing D))
    (hIpow : ∃ γ : Element,
      I ^ p = Ideal.span ({ofElement (D := D) γ} : Set (OmegaRing D))) :
    ∃ (k : ℕ) (beta : Element),
      k < p ∧ I * P ^ k =
        Ideal.span ({ofElement (D := D) beta} : Set (OmegaRing D)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Finite (ClassGroup (OmegaRing D)) := hh.finite
  obtain ⟨γ, hγ⟩ := hIpow
  by_cases hIbot : I = ⊥
  · refine ⟨0, (0, 0), Nat.pos_of_ne_zero hp.ne_zero, ?_⟩
    subst hIbot
    have hspan : Ideal.span ({ofElement (D := D) ((0, 0) : Element)} :
        Set (OmegaRing D)) = ⊥ := by
      change Ideal.span ({(⟨(0 : ℤ), 0⟩ : OmegaRing D)} : Set _) = ⊥
      exact Ideal.span_singleton_eq_bot.2 rfl
    rw [pow_zero, Ideal.bot_mul, hspan]
  · have hI_mem : I ∈ (Ideal (OmegaRing D))⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hIbot
    have hP_mem : P ∈ (Ideal (OmegaRing D))⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (ideal_ne_bot_of_two_mem h2)
    set cP : ClassGroup (OmegaRing D) := ClassGroup.mk0 ⟨P, hP_mem⟩
    set cI : ClassGroup (OmegaRing D) := ClassGroup.mk0 ⟨I, hI_mem⟩
    have hPord : orderOf cP = p :=
      order_eq_p_of_P (D := D) hP h2 hnp
    have hcIp : cI ^ p = 1 :=
      mk0_pow_eq_one_of_principal hI_mem ⟨ofElement (D := D) γ, hγ⟩
    have hp2G : ¬(p * p ∣ Nat.card (ClassGroup (OmegaRing D))) := by
      rw [hh.card_eq]; exact hp2
    have hmem : cI ∈ zpowers cP :=
      mem_zpowers_of_pow_eq_one hp hPord hcIp hp2G
    obtain ⟨k, hk, hmul⟩ :=
      exists_nat_lt_order_mul_eq_one (Nat.pos_of_ne_zero hp.ne_zero) hPord hmem
    have hPk_mem : P ^ k ∈ (Ideal (OmegaRing D))⁰ :=
      pow_mem_nonZeroDivisors_ideal hP_mem k
    have hprod_mem : I * P ^ k ∈ (Ideal (OmegaRing D))⁰ :=
      (mul_mem_nonZeroDivisors).2 ⟨hI_mem, hPk_mem⟩
    have hclass : ClassGroup.mk0 ⟨I * P ^ k, hprod_mem⟩ = 1 := by
      have hmap :
          ClassGroup.mk0 ⟨I, hI_mem⟩ *
            ClassGroup.mk0 ⟨P ^ k, hPk_mem⟩ =
            ClassGroup.mk0 ⟨I * P ^ k, hprod_mem⟩ := by
        convert (map_mul (ClassGroup.mk0 (R := OmegaRing D))
          ⟨I, hI_mem⟩ ⟨P ^ k, hPk_mem⟩).symm
      have hPk_class : ClassGroup.mk0 ⟨P ^ k, hPk_mem⟩ = cP ^ k := by
        change ClassGroup.mk0 ((⟨P, hP_mem⟩ : (Ideal (OmegaRing D))⁰) ^ k) =
          ClassGroup.mk0 ⟨P, hP_mem⟩ ^ k
        exact map_pow _ _ _
      calc
        ClassGroup.mk0 ⟨I * P ^ k, hprod_mem⟩
            = ClassGroup.mk0 ⟨I, hI_mem⟩ * ClassGroup.mk0 ⟨P ^ k, hPk_mem⟩ :=
              hmap.symm
        _ = cI * cP ^ k := by rw [hPk_class]
        _ = 1 := hmul
    have hprin : Submodule.IsPrincipal (I * P ^ k) :=
      (ClassGroup.mk0_eq_one_iff _).1 hclass
    haveI := hprin
    let βΩ := Submodule.IsPrincipal.generator (I * P ^ k)
    refine ⟨k, toElement βΩ, hk, ?_⟩
    calc
      I * P ^ k
          = Ideal.span {βΩ} := (Ideal.span_singleton_generator (I * P ^ k)).symm
      _ = Ideal.span {ofElement (D := D) (toElement βΩ)} := by
            rw [ofElement_toElement]

/-! ## Project bases -/

theorem p_exact_card_167 : ¬(11 * 11 ∣ (11 : ℕ)) := by decide
theorem p_exact_card_2471 : ¬(31 * 31 ∣ (62 : ℕ)) := by decide

theorem principalizer_167 (hh : classGroupOrder_167)
    (I : Ideal (OmegaRing 42))
    (hI : ∃ γ : Element,
      I ^ 11 = Ideal.span ({ofElement (D := 42) γ} : Set (OmegaRing 42))) :
    ∃ (k : ℕ) (beta : Element),
      k < 11 ∧ I * P167 ^ k =
        Ideal.span ({ofElement (D := 42) beta} : Set (OmegaRing 42)) :=
  exists_principalizer_of_classGroupOrder (D := 42) (eta := eta167) (p := 11)
    (h := 11) (P := P167) hh (by decide) p_exact_card_167 P167_pow two_mem_P167
    P167_not_principal I hI

set_option maxRecDepth 4096 in
theorem principalizer_2471 (hh : classGroupOrder_2471)
    (I : Ideal (OmegaRing 618))
    (hI : ∃ γ : Element,
      I ^ 31 = Ideal.span ({ofElement (D := 618) γ} : Set (OmegaRing 618))) :
    ∃ (k : ℕ) (beta : Element),
      k < 31 ∧ I * P2471 ^ k =
        Ideal.span ({ofElement (D := 618) beta} : Set (OmegaRing 618)) :=
  exists_principalizer_of_classGroupOrder (D := 618) (eta := eta2471) (p := 31)
    (h := 62) (P := P2471) hh (by decide) p_exact_card_2471 P2471_pow two_mem_P2471
    P2471_not_principal I hI

/-! ## IdealAPI-shaped specializations (`DedekindGap.principalizer`) -/

/-- `DedekindGap.principalizer` for `idealAPI167`, under `classGroupOrder_167`. -/
theorem principalizer_idealAPI167 (hh : classGroupOrder_167)
    (I : idealAPI167.Ideal)
    (hI : ∃ γ : Element, idealAPI167.powI I 11 = idealAPI167.principal γ) :
    ∃ (k : ℕ) (beta : Element),
      k < 11 ∧
        idealAPI167.mulI I (idealAPI167.powI P167 k) =
          idealAPI167.principal beta :=
  principalizer_167 hh I hI

set_option maxRecDepth 4096 in
/-- `DedekindGap.principalizer` for `idealAPI2471`, under `classGroupOrder_2471`. -/
theorem principalizer_idealAPI2471 (hh : classGroupOrder_2471)
    (I : idealAPI2471.Ideal)
    (hI : ∃ γ : Element, idealAPI2471.powI I 31 = idealAPI2471.principal γ) :
    ∃ (k : ℕ) (beta : Element),
      k < 31 ∧
        idealAPI2471.mulI I (idealAPI2471.powI P2471 k) =
          idealAPI2471.principal beta :=
  principalizer_2471 hh I hI

end Beal.OmegaRingPrincipalizer

#print axioms Beal.OmegaRingPrincipalizer.principalizer_167
#print axioms Beal.OmegaRingPrincipalizer.principalizer_2471
#print axioms Beal.OmegaRingPrincipalizer.principalizer_idealAPI167
#print axioms Beal.OmegaRingPrincipalizer.principalizer_idealAPI2471
