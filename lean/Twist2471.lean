import Std

/-! The finite intersection in the class-group descent for 2471³ + B⁴ = C³¹.
`powerTest` is only required to accept every 31st power; `powerTest_sound`
checks that implication for each modulus, including the nonfield Z/961Z. -/
namespace Beal.Twist2471

structure Place where
  modulus : Nat
  root : Nat
  testExponent : Nat
  deriving DecidableEq

def places : List Place := [⟨961, 90, 30⟩, ⟨683, 332, 22⟩, ⟨1117, 552, 36⟩, ⟨2791, 1030, 90⟩]

def eta (m s : Nat) := (90621 + 391 * s) * ((m + 1) / 2) % m

def powerTest (p : Place) (z : Nat) := z == 0 || z ^ p.testExponent % p.modulus == 1

def value (p : Place) (s k b : Nat) := eta p.modulus s ^ k * (b ^ 2 + 2471 * s) % p.modulus

def survives (p : Place) (k : Nat) := (List.range p.modulus).any fun b =>
  powerTest p (value p p.root k b) && powerTest p (value p (p.modulus - p.root) k b)

def LocalWitness (p : Place) (k : Nat) : Prop := ∃ b < p.modulus,
  (∃ x < p.modulus, x ^ 31 % p.modulus = value p p.root k b) ∧
  (∃ y < p.modulus, y ^ 31 % p.modulus = value p (p.modulus - p.root) k b)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Both substitutions respect the square relation in the ring of integers. -/
theorem root_checks : places.all (fun p => [p.root, p.modulus - p.root].all
    (fun s => (s ^ 2 + 2471) % p.modulus == 0)) = true := by decide

/-- This finite check justifies using the faster power test to reject a witness. -/
theorem powerTest_sound : places.all (fun p => (List.range p.modulus).all
    (fun x => powerTest p (x ^ 31 % p.modulus))) = true := by decide

theorem survives_of_witness {p : Place} (hp : p ∈ places) {k : Nat}
    (hw : LocalWitness p k) : survives p k = true := by
  have accepts := List.all_eq_true.mp (List.all_eq_true.mp powerTest_sound p hp)
  obtain ⟨b, hb, ⟨x, hx, ex⟩, ⟨y, hy, ey⟩⟩ := hw
  apply List.any_eq_true.mpr
  refine ⟨b, List.mem_range.mpr hb, ?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨ex ▸ accepts x (List.mem_range.mpr hx),
                                   ey ▸ accepts y (List.mem_range.mpr hy)⟩

theorem at961 : (List.range 31).filter (survives ⟨961, 90, 30⟩) =
    [1, 2, 6, 7, 8, 9, 12, 16, 19, 20, 22, 23, 29] := by decide

theorem at683 : [1, 2, 6, 7, 8, 9, 12, 16, 19, 20, 22, 23, 29].filter
    (survives ⟨683, 332, 22⟩) = [19, 23] := by decide

theorem at1117 : [19, 23].filter (survives ⟨1117, 552, 36⟩) = [19] := by decide

theorem at2791 : [19].filter (survives ⟨2791, 1030, 90⟩) = [] := by decide

/-- No single twist index has local witnesses at all four places. -/
theorem no_local_witnesses (k : Nat) (hk : k < 31)
    (hw : ∀ p ∈ places, LocalWitness p k) : False := by
  have good (p : Place) (hp : p ∈ places) := survives_of_witness hp (hw p hp)
  have h₁ := List.mem_filter.mpr ⟨List.mem_range.mpr hk, good ⟨961, 90, 30⟩ (by decide)⟩
  rw [at961] at h₁
  have h₂ := List.mem_filter.mpr ⟨h₁, good ⟨683, 332, 22⟩ (by decide)⟩
  rw [at683] at h₂
  have h₃ := List.mem_filter.mpr ⟨h₂, good ⟨1117, 552, 36⟩ (by decide)⟩
  rw [at1117] at h₃
  have h₄ := List.mem_filter.mpr ⟨h₃, good ⟨2791, 1030, 90⟩ (by decide)⟩
  rw [at2791] at h₄
  exact List.not_mem_nil h₄

end Beal.Twist2471

#print axioms Beal.Twist2471.no_local_witnesses
