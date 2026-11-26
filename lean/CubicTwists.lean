import Std

/-! Local exclusions for the even-`c` branch of `d^x + b^4 = c^3`.
The six representatives `x = 2*t + 1` have `t : Fin 6`. -/
namespace Beal.CubicTwists

inductive Base where
  | d167
  | d2471

def d : Base → Nat
  | .d167 => 167
  | .d2471 => 2471

def modulus (D : Base) (t : Fin 6) : Nat :=
  match D with
  | .d167 => if t.val == 1 || t.val == 4 then 19 else 9
  | .d2471 => 13

/-- One square root of `-d` in the indicated residue ring. -/
def root : Base → Nat
  | .d167 => 2
  | .d2471 => 5

theorem root_squares (D : Base) :
    ∀ t : Fin 6, (root D ^ 2 + d D) % modulus D t = 0 := by
  cases D <;> decide

/-- Reduction of eta_Q^k (b² + d^t s)/2 at the selected image of s.
The root of -d at P modulo 4 determines the orientation of eta_Q. -/
def value (D : Base) (t : Fin 6) (s b : Nat) : Nat :=
  let m := modulus D t
  let half := (m + 1) / 2
  let (trace, coeff, rootAtP, k) := match D with
    | .d167 => (3, 7, 3, 1)
    | .d2471 => (90621, 391, 1, 2)
  let a := d D ^ t.val
  let etaRoot := if (1 + a * rootAtP) % 4 = 0 then s else m - s
  let eta := (trace + coeff * etaRoot) * half % m
  (eta ^ k * (b ^ 2 + a * s) * half) % m

def IsCube (m target : Nat) : Prop :=
  ∃ u < m, u ^ 3 % m = target

instance (m target : Nat) : Decidable (IsCube m target) :=
  inferInstanceAs (Decidable (∃ u < m, u ^ 3 % m = target))

/-- For each base, exponent representative and b residue, at least one
embedding fails the cube test. Each embedding can choose its own cube root. -/
theorem no_local_cubes (D : Base) :
    ∀ (t : Fin 6) (b : Fin (modulus D t)),
      ¬ (IsCube (modulus D t) (value D t (root D) b.val) ∧
         IsCube (modulus D t) (value D t (modulus D t - root D) b.val)) := by
  cases D <;> decide

end Beal.CubicTwists

#print axioms Beal.CubicTwists.no_local_cubes
