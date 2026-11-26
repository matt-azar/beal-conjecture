import Std

/-! Finite part of the ideal-class descent for 167³ + B⁴ = C¹¹.
`admissibleTwists` tests each b against *both* conjugate embeddings. The b
witness can vary between moduli. Only the twist index must be shared. -/
namespace Beal.Twist167

def roots (m : Nat) : List Nat :=
  (List.range m).filter fun s => (s ^ 2 + 167) % m == 0

/-- For an odd modulus, `(m + 1) / 2` represents the inverse of 2. -/
def eta (m s : Nat) : Nat := ((3 + 7 * s) * ((m + 1) / 2)) % m

def powers (m : Nat) : List Nat :=
  ((List.range m).map (fun x => x ^ 11 % m)).eraseDups

def admissibleTwists (m s t : Nat) : List Nat :=
  (List.range 11).filter fun k =>
    let test := fun (r b : Nat) =>
      (powers m).contains ((eta m r ^ k * (b ^ 2 + 167 * r)) % m)
    (List.range m).any fun b => test s b && test t b

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem roots121 : roots 121 = [14, 107] := by decide

theorem roots199 : roots 199 = [80, 119] := by decide

theorem twists121 : admissibleTwists 121 14 107 = [0, 1, 4, 6] := by decide

theorem twists199 : admissibleTwists 199 80 119 = [2, 3, 5, 7, 8, 9, 10] := by decide

/-- Explicit witnesses for the two reductions with the same b. -/
def LocalWitness (m s t k : Nat) : Prop :=
  ∃ b < m, (∃ x < m, x ^ 11 % m = (eta m s ^ k * (b ^ 2 + 167 * s)) % m) ∧
           (∃ y < m, y ^ 11 % m = (eta m t ^ k * (b ^ 2 + 167 * t)) % m)

theorem powers_complete : [121, 199].all (fun m => (List.range m).all
    (fun x => (powers m).contains (x ^ 11 % m))) = true := by decide

theorem admissible_of_witness {m s t k : Nat} (hm : m ∈ [121, 199])
    (hk : k < 11) (hw : LocalWitness m s t k) : k ∈ admissibleTwists m s t := by
  have accepts := List.all_eq_true.mp (List.all_eq_true.mp powers_complete m hm)
  obtain ⟨b, hb, ⟨x, hx, ex⟩, ⟨y, hy, ey⟩⟩ := hw
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr hk, List.any_eq_true.mpr ⟨b, List.mem_range.mpr hb, ?_⟩⟩
  dsimp only
  rw [← ex, ← ey]
  exact Bool.and_eq_true_iff.mpr ⟨accepts x (List.mem_range.mpr hx),
                                   accepts y (List.mem_range.mpr hy)⟩

/-- The two complete local sieves have no common twist index. -/
theorem incompatible (k : Nat)
    (h₁ : k ∈ admissibleTwists 121 14 107)
    (h₂ : k ∈ admissibleTwists 199 80 119) : False := by
  rw [twists121] at h₁
  rw [twists199] at h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  omega

/-- The two moduli may use different witnesses, but must use the same k. -/
theorem no_local_witnesses (k : Nat) (hk : k < 11)
    (h₁ : LocalWitness 121 14 107 k) (h₂ : LocalWitness 199 80 119 k) : False :=
  incompatible k (admissible_of_witness (by decide) hk h₁)
                 (admissible_of_witness (by decide) hk h₂)

end Beal.Twist167

#print axioms Beal.Twist167.no_local_witnesses
