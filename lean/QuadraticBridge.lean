import Twist167
import Twist2471

/-! Reduction of a principalized twist in the full quadratic order. A pair
`(a,b)` encodes `a + bω` for `ω = (1+√(-d))/2` and `ω² = ω - D`,
where `D = (1+d)/4`. Coefficients, including those of the root, are signed.
The existence of a principalized twist from an integer solution is the
ideal-theoretic input to this file. -/
namespace Beal.QuadraticBridge

theorem pow_mod_congr {a b m : Nat} (h : a % m = b % m) (n : Nat) :
    a^n % m = b^n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

/-- The factorization into coprime conjugate ideals requires an odd right base. -/
theorem right_base_is_odd {d b c x p : Nat} (hd : d % 16 = 7) (hx : x % 2 = 1)
    (hp : 4 ≤ p) (eqn : d^x + b^4 = c^p) : c % 2 = 1 := by
  have d2 : d^2 % 16 = 1 := pow_mod_congr (b := 7) (m := 16) hd 2
  have dx : d^x % 16 = 7 := by
    have odd : x = 2 * (x/2) + 1 := by omega
    conv => lhs; rw [odd, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod]
    rw [pow_mod_congr (b := 1) (m := 16) d2, Nat.one_pow, hd]
  have b4 : b^4 % 16 = 0 ∨ b^4 % 16 = 1 := by
    have table : (List.range 16).all (fun a => a^4 % 16 == 0 || a^4 % 16 == 1) = true := by decide
    have hb := List.all_eq_true.mp table (b%16) (List.mem_range.mpr (Nat.mod_lt b (by decide)))
    have h : b^4 % 16 = (b%16)^4 % 16 :=
      pow_mod_congr (Nat.mod_mod b 16).symm 4
    simpa [h, Bool.or_eq_true, beq_iff_eq] using hb
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hc
    have four : 16 ∣ c^4 := by rw [ht, Nat.mul_pow]; exact ⟨t^4, rfl⟩
    have cp := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans four (Nat.pow_dvd_pow c hp))
    have h := congrArg (fun a => a % 16) eqn
    change (d^x + b^4) % 16 = c^p % 16 at h
    rw [Nat.add_mod, dx, cp] at h
    rcases b4 with hb | hb <;> rw [hb] at h <;> contradiction
  · exact hc

abbrev Element := Int × Int

def mul (D : Int) (u v : Element) : Element :=
  (u.1 * v.1 - D * u.2 * v.2, u.1 * v.2 + u.2 * v.1 + u.2 * v.2)

def pow (D : Int) (u : Element) : Nat → Element
  | 0 => (1, 0)
  | n+1 => mul D (pow D u n) u

def eval (w : Int) (u : Element) : Int := u.1 + u.2 * w

/-- b² + d√(-d), expressed in the integral basis 1, ω. -/
def gamma (d : Nat) (b : Int) : Element := (b^2 - d, 2 * d)


/-- Field norm in the integral basis (1, ω), with trace(ω)=1 and norm(ω)=D. -/
def norm (D : Int) (u : Element) : Int := u.1*u.1 + u.1*u.2 + D*u.2*u.2

/-- The original cubic equation supplies the norm identity used in the descent. -/
theorem norm_gamma_of_solution {d : Nat} {D b c : Int} {p : Nat}
    (hD : 4*D = (d : Int)+1) (eqn : (d : Int)^3+b^4 = c^p) :
    norm D (gamma d b) = c^p := by
  rw [← eqn, Int.add_comm]
  change (b^2-(d : Int))*(b^2-d)+(b^2-d)*(2*d)+D*(2*d)*(2*d) = _
  have h₄ : D+D+D+D = (d : Int)+1 := by omega
  have h₂ : 2*(d : Int) = d+d := by omega
  rw [h₂]
  have t := congrArg (fun x : Int => x*d*d) h₄
  simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add, Int.pow_succ, Int.pow_zero,
    Int.one_mul, Int.mul_one, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at t ⊢
  omega

def Cong (m : Nat) (a b : Int) : Prop := a % (m : Int) = b % (m : Int)

private theorem add_cong {m : Nat} {a b c d : Int} (h : Cong m a b) (g : Cong m c d) :
    Cong m (a+c) (b+d) := by
  unfold Cong at *
  rw [Int.add_emod a c, Int.add_emod b d, h, g]

private theorem mul_cong {m : Nat} {a b c d : Int} (h : Cong m a b) (g : Cong m c d) :
    Cong m (a*c) (b*d) := by
  unfold Cong at *
  rw [Int.mul_emod a c, Int.mul_emod b d, h, g]

private theorem pow_cong {m : Nat} {a b : Int} (h : Cong m a b) (n : Nat) :
    Cong m (a^n) (b^n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact mul_cong ih h

private theorem eval_mul {m : Nat} {D w : Int} (hw : Cong m (w-D-w*w) 0)
    (u v : Element) : Cong m (eval w (mul D u v)) (eval w u * eval w v) := by
  have expand : eval w (mul D u v) =
      eval w u * eval w v + u.2 * v.2 * (w-D-w*w) := by
    simp only [eval, mul, Int.add_mul, Int.mul_add, Int.mul_sub, Int.sub_mul,
               Int.mul_left_comm, Int.mul_comm, Int.mul_assoc]
    omega
  rw [expand]
  have h := add_cong (m := m) (a := eval w u * eval w v) rfl
    (mul_cong (a := u.2*v.2) rfl hw)
  simpa using h

private theorem eval_pow {m : Nat} {D w : Int} (hw : Cong m (w-D-w*w) 0)
    (u : Element) (n : Nat) : Cong m (eval w (pow D u n)) ((eval w u)^n) := by
  induction n with
  | zero => simp [pow, eval, Cong]
  | succ n ih =>
    exact Eq.trans (eval_mul hw (pow D u n) u) (mul_cong ih rfl)

def residue (m : Nat) (x : Int) : Nat := (x % (m : Int)).toNat

private theorem residue_lt {m : Nat} (hm : 0 < m) (x : Int) : residue m x < m := by
  have hm' : (0 : Int) < m := by omega
  exact (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr (Int.emod_lt_of_pos _ hm')

private theorem residue_cong {m : Nat} (hm : 0 < m) (x : Int) :
    Cong m (residue m x) x := by
  unfold Cong residue
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_emod]

/-- Conditions on a single reduction. Here w represents ω, s represents √(-d),
and e is the residue used for η by the finite certificate. -/
def Reduction (D : Int) (eta : Element) (m s e : Nat) (w : Int) : Prop :=
  0 < m ∧ Cong m (w-D-w*w) 0 ∧ Cong m (2*w-1) s ∧ Cong m (eval w eta) e

instance (D : Int) (eta : Element) (m s e : Nat) (w : Int) :
    Decidable (Reduction D eta m s e w) := by unfold Reduction Cong; infer_instance

/-- One bounded local root obtained from a global integral root. -/
theorem reduce_twist {D : Int} {eta beta : Element} {d p k m s e : Nat} {w b : Int}
    (red : Reduction D eta m s e w)
    (identity : pow D beta p = mul D (pow D eta k) (gamma d b)) :
    ∃ x < m, x^p % m = (e^k * ((residue m b)^2 + d*s)) % m := by
  obtain ⟨hm, hw, hs, he⟩ := red
  refine ⟨residue m (eval w beta), residue_lt hm _, ?_⟩
  have hgamma : eval w (gamma d b) = b^2 + (d : Int)*(2*w-1) := by
    simp [eval, gamma, Int.mul_sub, Int.mul_left_comm, Int.mul_comm, Int.mul_assoc]
    omega
  have hg : Cong m (eval w (gamma d b)) ((residue m b : Int)^2 + (d : Int)*s) := by
    rw [hgamma]
    exact add_cong (pow_cong (Eq.symm (residue_cong hm b)) 2) (mul_cong rfl hs)
  have h : Cong m ((residue m (eval w beta) : Int)^p)
      ((e : Int)^k * ((residue m b : Int)^2 + (d : Int)*s)) := calc
    _ = _ := pow_cong (residue_cong hm _) p
    _ = _ := Eq.symm (eval_pow hw beta p)
    _ = _ := congrArg (fun z => eval w z % (m : Int)) identity
    _ = _ := eval_mul hw _ _
    _ = _ := mul_cong (Eq.trans (eval_pow hw eta k) (pow_cong he k)) hg
  apply Int.ofNat_inj.mp
  simpa only [Int.ofNat_emod, Int.ofNat_mul, Int.ofNat_add, Int.natCast_pow] using h

/-- Representative of (1+s)/2 at an odd modulus. Its required identities are
checked for each embedding, including those modulo 11² and 31². -/
def omegaResidue (m s : Nat) : Int := ((1+s)*((m+1)/2) % m : Nat)

abbrev eta167 : Element := (-2, 7)
abbrev eta2471 : Element := (45115, 391)

private theorem local167 {beta : Element} {k m s t : Nat} {b : Int}
    (h : pow 42 beta 11 = mul 42 (pow 42 eta167 k) (gamma 167 b))
    (hs : Reduction 42 eta167 m s (Twist167.eta m s) (omegaResidue m s))
    (ht : Reduction 42 eta167 m t (Twist167.eta m t) (omegaResidue m t)) :
    Twist167.LocalWitness m s t k :=
  ⟨residue m b, residue_lt hs.1 _, reduce_twist hs h, reduce_twist ht h⟩

/-- The principalized twist equation has no integral root for any allowed
ideal-class index in Z[(1+√(-167))/2]. -/
theorem no_integral_twist167 (b : Int) (beta : Element) (k : Nat) (hk : k < 11)
    (h : pow 42 beta 11 = mul 42 (pow 42 eta167 k) (gamma 167 b)) : False :=
  Twist167.no_local_witnesses k hk (local167 h (by decide) (by decide))
                                  (local167 h (by decide) (by decide))

private theorem reductions2471 (v : Twist2471.Place) (hv : v ∈ Twist2471.places) :
    Reduction 618 eta2471 v.modulus v.root (Twist2471.eta v.modulus v.root)
      (omegaResidue v.modulus v.root) ∧
    Reduction 618 eta2471 v.modulus (v.modulus-v.root)
      (Twist2471.eta v.modulus (v.modulus-v.root))
      (omegaResidue v.modulus (v.modulus-v.root)) := by
  simp only [Twist2471.places, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

/-- The principalized twist equation has no integral root for any allowed
ideal-class index in Z[(1+√(-2471))/2]. -/
theorem no_integral_twist2471 (b : Int) (beta : Element) (k : Nat) (hk : k < 31)
    (h : pow 618 beta 31 = mul 618 (pow 618 eta2471 k) (gamma 2471 b)) : False := by
  apply Twist2471.no_local_witnesses k hk
  intro v hv
  obtain ⟨hs, ht⟩ := reductions2471 v hv
  exact ⟨residue v.modulus b, residue_lt hs.1 _, reduce_twist hs h, reduce_twist ht h⟩

end Beal.QuadraticBridge

#print axioms Beal.QuadraticBridge.no_integral_twist167
#print axioms Beal.QuadraticBridge.no_integral_twist2471
#print axioms Beal.QuadraticBridge.right_base_is_odd
