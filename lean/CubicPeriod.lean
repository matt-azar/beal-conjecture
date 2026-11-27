import CubicTwists
import QuadraticBridge
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
Period of the cubic residue certificate and the bridge from an even-`c`
solution of `d^x + b^4 = c^3` to the input of `CubicTwists.no_local_cubes`.

Paper: `docs/right-exponent-three.md` (“Odd x and even c”).

1. `CubicGap` is the cubic analogue of `DedekindGap`: from the ideal
   factorization it supplies the oriented identity `β³ = η_Q^k δ`.
2. The odd exponent is periodic modulo 12 for the certificate.
3. Reducing the identity at both embeddings yields the input of
   `no_local_cubes`, hence a contradiction.

No `sorry` and no new `axiom`.
-/
namespace Beal.CubicPeriod
open QuadraticBridge
open Beal.CubicTwists

/-! ## Base data -/

def omegaD : Base → Int
  | .d167 => 42
  | .d2471 => 618

def etaElement : Base → Element
  | .d167 => eta167
  | .d2471 => eta2471

def twistK : Base → Nat
  | .d167 => 1
  | .d2471 => 2

def rootAtP : Base → Nat
  | .d167 => 3
  | .d2471 => 1

def traceEta : Base → Nat
  | .d167 => 3
  | .d2471 => 90621

def coeffEta : Base → Nat
  | .d167 => 7
  | .d2471 => 391

def conjugateElement (u : Element) : Element := (u.1 + u.2, -u.2)

def usesEta (B : Base) (t : Nat) : Bool :=
  decide ((1 + (d B) ^ t * rootAtP B) % 4 = 0)

def etaQ (B : Base) (t : Nat) : Element :=
  if usesEta B t then etaElement B else conjugateElement (etaElement B)

/-- `δ = (b² + a s)/2` in the ω-basis. -/
def delta (a b : Int) : Element := ((b ^ 2 - a) / 2, a)

def etaResidue (B : Base) (t m s : Nat) : Nat :=
  let half := (m + 1) / 2
  let etaRoot := if usesEta B t then s else m - s
  (traceEta B + coeffEta B * etaRoot) * half % m

def localTarget (B : Base) (t : Fin 6) (s b : Nat) : Nat :=
  let m := modulus B t
  (etaResidue B t.val m s ^ twistK B *
    (b ^ 2 + d B ^ t.val * s) * ((m + 1) / 2)) % m

theorem value_eq_localTarget (B : Base) (t : Fin 6) (s b : Nat) :
    value B t s b = localTarget B t s b := by
  cases B <;> fin_cases t <;> rfl

/-! ## Congruence helpers -/

private theorem add_cong {m : Nat} {a b c e : Int} (h : Cong m a b) (g : Cong m c e) :
    Cong m (a + c) (b + e) := by
  unfold Cong at *; rw [Int.add_emod a c, Int.add_emod b e, h, g]

private theorem mul_cong {m : Nat} {a b c e : Int} (h : Cong m a b) (g : Cong m c e) :
    Cong m (a * c) (b * e) := by
  unfold Cong at *; rw [Int.mul_emod a c, Int.mul_emod b e, h, g]

private theorem pow_cong {m : Nat} {a b : Int} (h : Cong m a b) (n : Nat) :
    Cong m (a ^ n) (b ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact mul_cong ih h

private theorem eval_mul {m : Nat} {D w : Int} (hw : Cong m (w - D - w * w) 0)
    (u v : Element) : Cong m (eval w (mul D u v)) (eval w u * eval w v) := by
  have expand : eval w (mul D u v) =
      eval w u * eval w v + u.2 * v.2 * (w - D - w * w) := by
    simp only [eval, mul, Int.add_mul, Int.mul_add, Int.mul_sub, Int.sub_mul,
               Int.mul_left_comm, Int.mul_comm, Int.mul_assoc]
    omega
  rw [expand]
  simpa using add_cong (m := m) (a := eval w u * eval w v) rfl
    (mul_cong (a := u.2 * v.2) rfl hw)

private theorem eval_pow {m : Nat} {D w : Int} (hw : Cong m (w - D - w * w) 0)
    (u : Element) (n : Nat) : Cong m (eval w (pow D u n)) ((eval w u) ^ n) := by
  induction n with
  | zero => simp [pow, eval, Cong]
  | succ n ih => exact Eq.trans (eval_mul hw (pow D u n) u) (mul_cong ih rfl)

private theorem residue_lt {m : Nat} (hm : 0 < m) (x : Int) : residue m x < m := by
  exact (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr
    (Int.emod_lt_of_pos _ (by exact_mod_cast hm))

private theorem residue_cong {m : Nat} (hm : 0 < m) (x : Int) :
    Cong m (residue m x) x := by
  unfold Cong residue
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_emod]

theorem two_mul_ediv_of_even {n : Int} (h : n % 2 = 0) : 2 * (n / 2) = n := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  have hk' : n = 2 * k := by rw [hk, Int.mul_comm]
  subst hk'
  have : (2 * k : Int) / 2 = k := by omega
  simp [this]

private theorem mul_mod_right_cancel (a b m : Nat) :
    (a * b) % m = (a * (b % m)) % m := by
  calc
    (a * b) % m = (a % m * (b % m)) % m := by rw [Nat.mul_mod]
    _ = (a % m * ((b % m) % m)) % m := by rw [Nat.mod_mod]
    _ = (a * (b % m)) % m := by rw [← Nat.mul_mod]

/-! ## Periodicity modulo 12 -/

theorem odd_exponent_mod_twelve {x : Nat} (hx : x % 2 = 1) :
    ∃ (t : Fin 6) (j : Nat), x = 12 * j + (2 * t.val + 1) := by
  have hdiv : 12 * (x / 12) + x % 12 = x := Nat.div_add_mod x 12
  have hlt : x % 12 < 12 := Nat.mod_lt x (by decide)
  have hodd : (x % 12) % 2 = 1 := by
    have : x % 2 = (x % 12) % 2 :=
      (Nat.mod_mod_of_dvd x (by decide : 2 ∣ 12)).symm
    omega
  let r := x % 12
  let tval := r / 2
  have htval : tval < 6 := by
    dsimp [tval, r]; omega
  have hr : r = 2 * tval + 1 := by
    dsimp [tval, r]; omega
  refine ⟨⟨tval, htval⟩, x / 12, ?_⟩
  calc
    x = 12 * (x / 12) + r := by
      dsimp [r]; exact hdiv.symm
    _ = 12 * (x / 12) + (2 * tval + 1) := by rw [hr]
    _ = 12 * (x / 12) + (2 * (⟨tval, htval⟩ : Fin 6).val + 1) := rfl

theorem usesEta_period (B : Base) (t j : Nat) :
    usesEta B (t + 6 * j) = usesEta B t := by
  simp only [usesEta]
  have hd4 : (d B) % 4 = 3 := by cases B <;> decide
  have d2 : (d B) ^ 2 % 4 = 1 := by
    have : (d B) ^ 2 % 4 = ((d B) % 4) ^ 2 % 4 :=
      pow_mod_congr (Nat.mod_mod (d B) 4).symm 2
    simpa [hd4] using this
  have d6 : (d B) ^ 6 % 4 = 1 := by
    have h6 : (d B) ^ 6 = ((d B) ^ 2) ^ 3 := by rw [← Nat.pow_mul]
    rw [h6]
    have : ((d B) ^ 2) ^ 3 % 4 = (1 : Nat) ^ 3 % 4 := pow_mod_congr d2 3
    simpa using this
  have ha : (d B) ^ (t + 6 * j) % 4 = (d B) ^ t % 4 := by
    rw [Nat.pow_add, Nat.mul_mod, Nat.pow_mul,
      pow_mod_congr (b := 1) (m := 4) d6, Nat.one_pow, Nat.mul_one, Nat.mod_mod]
  have hpow :
      (1 + (d B) ^ (t + 6 * j) * rootAtP B) % 4
        = (1 + (d B) ^ t * rootAtP B) % 4 := by
    have hmul :
        ((d B) ^ (t + 6 * j) * rootAtP B) % 4
          = ((d B) ^ t * rootAtP B) % 4 := by
      rw [Nat.mul_mod, ha, ← Nat.mul_mod]
    rw [Nat.add_mod, hmul, ← Nat.add_mod]
  rw [hpow]

theorem etaQ_period (B : Base) (t j : Nat) :
    etaQ B (t + 6 * j) = etaQ B t := by
  simp only [etaQ, usesEta_period]

theorem etaResidue_period (B : Base) (t j m s : Nat) :
    etaResidue B (t + 6 * j) m s = etaResidue B t m s := by
  simp only [etaResidue, usesEta_period]

/-- Cube root of the period factor `d^{6j}`. -/
def periodCubeRoot (B : Base) (j : Nat) : Nat := d B ^ (2 * j)

theorem d_six_j_is_cube (B : Base) (j : Nat) :
    d B ^ (6 * j) = (periodCubeRoot B j) ^ 3 := by
  simp only [periodCubeRoot]
  calc
    d B ^ (6 * j) = d B ^ (3 * (2 * j)) := by ring
    _ = (d B ^ 3) ^ (2 * j) := by rw [Nat.pow_mul]
    _ = (d B ^ (2 * j)) ^ 3 := by rw [Nat.pow_right_comm]

/-! ## CubicGap -/

/-- Cubic analogue of `DedekindGap` for the even-`c` branch at right
exponent 3. Supplies the oriented identity `β³ = η_Q^k δ` produced by the
ideal factorization in `docs/right-exponent-three.md`. -/
structure CubicGap (B : Base) where
  oriented_cube :
    ∀ (b c : Int) (x : Nat),
      x % 2 = 1 →
      c % 2 = 0 →
      ((d B : Int) ^ x + b ^ 4 = c ^ 3) →
      ∃ beta : Element,
        pow (omegaD B) beta 3
          = mul (omegaD B)
              (pow (omegaD B) (etaQ B ((x - 1) / 2)) (twistK B))
              (delta ((d B : Int) ^ ((x - 1) / 2)) b)

/-! ## Parity -/

theorem b_odd_of_even_c {B : Base} {b c : Int} {x : Nat}
    (hc : c % 2 = 0)
    (eqn : (d B : Int) ^ x + b ^ 4 = c ^ 3) :
    b % 2 = 1 := by
  have hd : (d B : Int) % 2 = 1 := by cases B <;> decide
  have dx : (d B : Int) ^ x % 2 = 1 := by
    clear eqn hc b c
    induction x with
    | zero => cases B <;> decide
    | succ x ih =>
      rw [Int.pow_succ, Int.mul_emod, ih, hd]; decide
  rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · have b4 : b ^ 4 % 2 = 0 := by
      have h2 : b ^ 2 % 2 = 0 := by
        rw [pow_two, Int.mul_emod, hb]; decide
      rw [show b ^ 4 = b ^ 2 * b ^ 2 from by ring, Int.mul_emod, h2]; decide
    have lhs : ((d B : Int) ^ x + b ^ 4) % 2 = 1 := by
      rw [Int.add_emod, dx, b4]; decide
    have rhs : c ^ 3 % 2 = 0 := by
      have h2 : c ^ 2 % 2 = 0 := by
        rw [pow_two, Int.mul_emod, hc]; decide
      rw [Int.pow_succ, Int.mul_emod, h2, hc]; decide
    have : ((d B : Int) ^ x + b ^ 4) % 2 = c ^ 3 % 2 :=
      congrArg (· % 2) eqn
    simp [lhs, rhs] at this
  · exact hb

theorem pow_odd_odd (B : Base) (n : Nat) : ((d B : Int) ^ n) % 2 = 1 := by
  have hd : (d B : Int) % 2 = 1 := by cases B <;> decide
  induction n with
  | zero => cases B <;> decide
  | succ n ih =>
    rw [Int.pow_succ, Int.mul_emod, ih, hd]; decide

/-! ## Finite reduction data -/

theorem reductions (B : Base) :
    ∀ t : Fin 6,
      let m := modulus B t
      let r := root B
      Reduction (omegaD B) (etaQ B t.val) m r
          (etaResidue B t.val m r) (omegaResidue m r) ∧
      Reduction (omegaD B) (etaQ B t.val) m (m - r)
          (etaResidue B t.val m (m - r)) (omegaResidue m (m - r)) := by
  intro t; revert t; cases B <;> decide

theorem half_inv (B : Base) :
    ∀ t : Fin 6, Cong (modulus B t) (((modulus B t + 1) / 2 : Nat) * 2) 1 := by
  intro t; unfold Cong; revert t; cases B <;> decide

theorem d_coprime_modulus (B : Base) :
    ∀ t : Fin 6, Nat.Coprime (d B) (modulus B t) := by
  intro t; revert t; cases B <;> decide

theorem modulus_gt_one (B : Base) :
    ∀ t : Fin 6, 1 < modulus B t := by
  intro t; revert t; cases B <;> decide

/-! ## Reduction of an oriented cubic twist -/

theorem cong_eval_delta {m : Nat} {w a b s : Int}
    (hm : 1 < m)
    (h2 : Cong m (((m + 1) / 2 : Nat) * 2) 1)
    (hs : Cong m (2 * w - 1) s)
    (heven : (b ^ 2 - a) % 2 = 0) :
    Cong m (eval w (delta a b))
      (((m + 1) / 2 : Nat) * (b ^ 2 + a * s)) := by
  have hexact : 2 * ((b ^ 2 - a) / 2) = b ^ 2 - a := two_mul_ediv_of_even heven
  have h2eval : eval w (delta a b) * 2 = b ^ 2 + a * (2 * w - 1) := by
    simp only [eval, delta]
    have : ((b ^ 2 - a) / 2 + a * w) * 2
        = 2 * ((b ^ 2 - a) / 2) + 2 * a * w := by ring
    rw [this, hexact]; ring
  have hcong2 : Cong m (eval w (delta a b) * 2) (b ^ 2 + a * s) := by
    unfold Cong
    rw [h2eval, Int.add_emod, Int.mul_emod a (2 * w - 1), hs,
      ← Int.mul_emod, ← Int.add_emod]
  have hmul := mul_cong (a := ((m + 1) / 2 : Nat)) rfl hcong2
  unfold Cong at h2 hmul ⊢
  have h1m : (1 : Int) % m = 1 := by
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm)
  have hleft :
      ((((m + 1) / 2 : Nat) : Int) * (eval w (delta a b) * 2)) % (m : Int)
        = eval w (delta a b) % (m : Int) := by
    calc
      ((((m + 1) / 2 : Nat) : Int) * (eval w (delta a b) * 2)) % (m : Int)
          = (((((m + 1) / 2 : Nat) : Int) * 2) * eval w (delta a b)) % (m : Int) := by
            ring_nf
      _ = (((((m + 1) / 2 : Nat) : Int) * 2 % (m : Int)) *
            (eval w (delta a b) % (m : Int))) % (m : Int) := by
            rw [Int.mul_emod]
      _ = ((1 : Int) % m * (eval w (delta a b) % (m : Int))) % (m : Int) := by
            rw [h2]
      _ = (1 * (eval w (delta a b) % (m : Int))) % (m : Int) := by rw [h1m]
      _ = eval w (delta a b) % (m : Int) := by
            rw [Int.one_mul, Int.emod_emod]
  exact hleft.symm.trans hmul

theorem reduce_cubic_twist {B : Base} {beta : Element} {t : Nat}
    {m s e : Nat} {w b : Int}
    (hm : 1 < m)
    (red : Reduction (omegaD B) (etaQ B t) m s e w)
    (heven : (b ^ 2 - (d B : Int) ^ t) % 2 = 0)
    (h2 : Cong m (((m + 1) / 2 : Nat) * 2) 1)
    (identity :
      pow (omegaD B) beta 3
        = mul (omegaD B) (pow (omegaD B) (etaQ B t) (twistK B))
            (delta ((d B : Int) ^ t) b)) :
    IsCube m
      ((e ^ twistK B * ((residue m b) ^ 2 + (d B) ^ t * s) * ((m + 1) / 2)) % m) := by
  obtain ⟨hm0, hw, hs, he⟩ := red
  refine ⟨residue m (eval w beta), residue_lt hm0 _, ?_⟩
  have hg : Cong m (eval w (delta ((d B : Int) ^ t) b))
      (((m + 1) / 2 : Nat) *
        ((residue m b : Int) ^ 2 + (d B : Int) ^ t * s)) := by
    have hδ := cong_eval_delta (m := m) (w := w) (a := (d B : Int) ^ t) (b := b)
      (s := 2 * w - 1) hm h2 (by rfl) heven
    have hfactor :
        Cong m
          (((m + 1) / 2 : Nat) * (b ^ 2 + (d B : Int) ^ t * (2 * w - 1)))
          (((m + 1) / 2 : Nat) *
            ((residue m b : Int) ^ 2 + (d B : Int) ^ t * s)) :=
      mul_cong rfl (add_cong (pow_cong (Eq.symm (residue_cong hm0 b)) 2)
        (mul_cong rfl hs))
    exact Eq.trans hδ hfactor
  have h : Cong m ((residue m (eval w beta) : Int) ^ 3)
      ((e : Int) ^ twistK B *
        ((residue m b : Int) ^ 2 + (d B : Int) ^ t * s) *
          ((m + 1) / 2 : Nat)) := by
    have h0 : Cong m ((residue m (eval w beta) : Int) ^ 3)
        ((e : Int) ^ twistK B *
          (((m + 1) / 2 : Nat) *
            ((residue m b : Int) ^ 2 + (d B : Int) ^ t * s))) := calc
      _ = _ := pow_cong (residue_cong hm0 _) 3
      _ = _ := Eq.symm (eval_pow hw beta 3)
      _ = _ := congrArg (fun z => eval w z % (m : Int)) identity
      _ = _ := eval_mul hw _ _
      _ = _ := mul_cong
                (Eq.trans (eval_pow hw (etaQ B t) (twistK B)) (pow_cong he _)) hg
    convert h0 using 1; ring
  unfold Cong at h
  apply Int.ofNat_inj.mp
  simpa [Int.natCast_pow, Int.natCast_mul, Int.natCast_add, Int.natCast_emod] using h

/-! ## Period cube transport -/

theorem isCube_of_mul_cube {m target u : Nat}
    (hu : Nat.Coprime u m) (hm : 1 < m)
    (h : IsCube m ((u ^ 3 * target) % m)) :
    IsCube m (target % m) := by
  obtain ⟨x, hx, hxeq⟩ := h
  obtain ⟨inv, hinv⟩ := Nat.exists_mul_emod_eq_one_of_coprime hu hm
  refine ⟨(x * inv) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm), ?_⟩
  have hrearr : u ^ 3 * target * inv ^ 3 = target * (u * inv) ^ 3 := by
    rw [Nat.mul_pow]; ring
  calc
    ((x * inv) % m) ^ 3 % m
        = (x * inv) ^ 3 % m := pow_mod_congr (Nat.mod_mod (x * inv) m) 3
    _ = (x ^ 3 * inv ^ 3) % m := by rw [Nat.mul_pow]
    _ = ((x ^ 3 % m) * (inv ^ 3 % m)) % m := by rw [Nat.mul_mod]
    _ = (((u ^ 3 * target) % m) * (inv ^ 3 % m)) % m := by rw [hxeq]
    _ = (u ^ 3 * target * inv ^ 3) % m := by rw [← Nat.mul_mod]
    _ = (target * (u * inv) ^ 3) % m := by rw [hrearr]
    _ = (target % m * ((u * inv) ^ 3 % m)) % m := by rw [Nat.mul_mod]
    _ = (target % m * (((u * inv) % m) ^ 3 % m)) % m := by
          rw [pow_mod_congr (Nat.mod_mod (u * inv) m) 3]
    _ = (target % m * (1 ^ 3 % m)) % m := by rw [hinv]
    _ = (target % m * (1 % m)) % m := by simp
    _ = target % m := by
          have h1 : 1 % m = 1 := Nat.mod_eq_of_lt hm
          rw [h1, Nat.mul_one, Nat.mod_mod]

theorem localTarget_period (B : Base) (t : Fin 6) (j s b0 : Nat) :
    let m := modulus B t
    let bLift := (b0 * d B ^ (3 * j)) % m
    (etaResidue B (t.val + 6 * j) m s ^ twistK B *
        (bLift ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m
      = (d B ^ (6 * j) * localTarget B t s b0) % m := by
  intro m bLift
  have hη := etaResidue_period B t.val j m s
  have ha : d B ^ (t.val + 6 * j) = d B ^ t.val * d B ^ (6 * j) :=
    Nat.pow_add _ _ _
  have hb2 : bLift ^ 2 % m = (b0 ^ 2 * d B ^ (6 * j)) % m := by
    dsimp [bLift]
    have : ((b0 * d B ^ (3 * j)) % m) ^ 2 % m
        = (b0 * d B ^ (3 * j)) ^ 2 % m :=
      pow_mod_congr (Nat.mod_mod _ _) 2
    have hpow : (b0 * d B ^ (3 * j)) ^ 2 = b0 ^ 2 * d B ^ (6 * j) := by
      rw [Nat.mul_pow]
      congr 1
      rw [← Nat.pow_mul]
      ring
    rw [this, hpow]
  have hsum :
      (bLift ^ 2 + d B ^ (t.val + 6 * j) * s) % m
        = (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s)) % m := by
    rw [ha]
    have hL :
        (bLift ^ 2 + d B ^ t.val * d B ^ (6 * j) * s) % m
          = (b0 ^ 2 * d B ^ (6 * j) + d B ^ (6 * j) * (d B ^ t.val * s)) % m := by
      have hright :
          (d B ^ t.val * d B ^ (6 * j) * s) % m
            = (d B ^ (6 * j) * (d B ^ t.val * s)) % m := by
        have : d B ^ t.val * d B ^ (6 * j) * s
            = d B ^ (6 * j) * (d B ^ t.val * s) := by ring
        rw [this]
      calc
        (bLift ^ 2 + d B ^ t.val * d B ^ (6 * j) * s) % m
            = (bLift ^ 2 % m + (d B ^ t.val * d B ^ (6 * j) * s) % m) % m := by
              rw [Nat.add_mod]
        _ = (b0 ^ 2 * d B ^ (6 * j) % m +
              (d B ^ (6 * j) * (d B ^ t.val * s)) % m) % m := by
              rw [hb2, hright]
        _ = (b0 ^ 2 * d B ^ (6 * j) +
              d B ^ (6 * j) * (d B ^ t.val * s)) % m := by
              rw [← Nat.add_mod]
    have hR :
        (b0 ^ 2 * d B ^ (6 * j) + d B ^ (6 * j) * (d B ^ t.val * s)) % m
          = (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s)) % m := by
      have : b0 ^ 2 * d B ^ (6 * j) + d B ^ (6 * j) * (d B ^ t.val * s)
          = d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s) := by ring
      rw [this]
    exact hL.trans hR
  have h1 :
      (etaResidue B (t.val + 6 * j) m s ^ twistK B *
          (bLift ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m
        = (etaResidue B t.val m s ^ twistK B *
            (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s)) * ((m + 1) / 2)) % m := by
    have hmul :
        (etaResidue B (t.val + 6 * j) m s ^ twistK B *
            (bLift ^ 2 + d B ^ (t.val + 6 * j) * s)) % m
          = (etaResidue B t.val m s ^ twistK B *
              (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s))) % m := by
      calc
        _ = (etaResidue B (t.val + 6 * j) m s ^ twistK B % m *
              ((bLift ^ 2 + d B ^ (t.val + 6 * j) * s) % m)) % m := by
            rw [Nat.mul_mod]
        _ = (etaResidue B t.val m s ^ twistK B % m *
              (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s) % m)) % m := by
            rw [hη, hsum]
        _ = _ := by rw [← Nat.mul_mod]
    calc
      (etaResidue B (t.val + 6 * j) m s ^ twistK B *
          (bLift ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m
          = ((etaResidue B (t.val + 6 * j) m s ^ twistK B *
              (bLift ^ 2 + d B ^ (t.val + 6 * j) * s)) % m *
              ((m + 1) / 2 % m)) % m := by
            rw [Nat.mul_mod]
      _ = ((etaResidue B t.val m s ^ twistK B *
              (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s))) % m *
              ((m + 1) / 2 % m)) % m := by rw [hmul]
      _ = _ := by rw [← Nat.mul_mod]
  refine h1.trans ?_
  have hrearr :
      etaResidue B t.val m s ^ twistK B *
          (d B ^ (6 * j) * (b0 ^ 2 + d B ^ t.val * s)) * ((m + 1) / 2)
        = d B ^ (6 * j) *
            (etaResidue B t.val m s ^ twistK B *
              (b0 ^ 2 + d B ^ t.val * s) * ((m + 1) / 2)) := by
    ring
  rw [hrearr]
  simp only [localTarget]
  exact mul_mod_right_cancel (d B ^ (6 * j)) _ m

/-! ## Main bridge -/

theorem local_cubes_of_identity {B : Base} {beta : Element}
    {t : Fin 6} {j : Nat} {b : Int}
    (hb_odd : b % 2 = 1)
    (identity :
      pow (omegaD B) beta 3
        = mul (omegaD B)
            (pow (omegaD B) (etaQ B (t.val + 6 * j)) (twistK B))
            (delta ((d B : Int) ^ (t.val + 6 * j)) b)) :
    ∃ b0 : Fin (modulus B t),
      IsCube (modulus B t) (value B t (root B) b0.val) ∧
      IsCube (modulus B t)
        (value B t (modulus B t - root B) b0.val) := by
  let m := modulus B t
  have hm1 : 1 < m := modulus_gt_one B t
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm1
  obtain ⟨hs0, ht0⟩ := reductions B t
  have heta := etaQ_period B t.val j
  have hηr (s : Nat) := etaResidue_period B t.val j m s
  have hs : Reduction (omegaD B) (etaQ B (t.val + 6 * j)) m (root B)
      (etaResidue B (t.val + 6 * j) m (root B)) (omegaResidue m (root B)) := by
    rw [heta, hηr]; exact hs0
  have ht : Reduction (omegaD B) (etaQ B (t.val + 6 * j)) m (m - root B)
      (etaResidue B (t.val + 6 * j) m (m - root B))
      (omegaResidue m (m - root B)) := by
    rw [heta, hηr]; exact ht0
  have heven : (b ^ 2 - (d B : Int) ^ (t.val + 6 * j)) % 2 = 0 := by
    have hb2 : b ^ 2 % 2 = 1 := by
      rw [pow_two, Int.mul_emod, hb_odd]; decide
    rw [Int.sub_emod, hb2, pow_odd_odd B (t.val + 6 * j)]; decide
  have h2 := half_inv B t
  have cube1 :=
    reduce_cubic_twist (B := B) (t := t.val + 6 * j) hm1 hs heven h2 identity
  have cube2 :=
    reduce_cubic_twist (B := B) (t := t.val + 6 * j) hm1 ht heven h2 identity
  have d_cop := d_coprime_modulus B t
  have d3_cop : Nat.Coprime (d B ^ (3 * j)) m := Nat.Coprime.pow_left _ d_cop
  obtain ⟨dInv, hdInv⟩ := Nat.exists_mul_emod_eq_one_of_coprime d3_cop hm1
  let b_res := residue m b
  let b0_nat : Nat := (b_res * dInv) % m
  refine ⟨⟨b0_nat, Nat.mod_lt _ hm0⟩, ?_⟩
  have hscale : b_res % m = (b0_nat * d B ^ (3 * j)) % m := by
    dsimp [b0_nat]
    calc
      b_res % m
          = (b_res * 1) % m := by rw [Nat.mul_one]
      _ = (b_res * ((d B ^ (3 * j) * dInv) % m)) % m := by rw [hdInv]
      _ = (b_res * (d B ^ (3 * j) * dInv)) % m := by
            exact (mul_mod_right_cancel b_res _ m).symm
      _ = (b_res * (dInv * d B ^ (3 * j))) % m := by
            rw [Nat.mul_comm (d B ^ (3 * j))]
      _ = (b_res * dInv * d B ^ (3 * j)) % m := by
            rw [← Nat.mul_assoc]
      _ = ((b_res * dInv) % m * (d B ^ (3 * j) % m)) % m := by
            rw [Nat.mul_mod]
      _ = ((b_res * dInv) % m * d B ^ (3 * j)) % m := by
            exact (mul_mod_right_cancel ((b_res * dInv) % m) (d B ^ (3 * j)) m).symm
  have u_cop : Nat.Coprime (periodCubeRoot B j) m :=
    Nat.Coprime.pow_left _ d_cop
  have transport (s : Nat)
      (hcube : IsCube m
        ((etaResidue B (t.val + 6 * j) m s ^ twistK B *
            (b_res ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m)) :
      IsCube m (value B t s b0_nat) := by
    have hp := localTarget_period B t j s b0_nat
    have hb2 :
        (b_res ^ 2 + d B ^ (t.val + 6 * j) * s) % m
          = (((b0_nat * d B ^ (3 * j)) % m) ^ 2
              + d B ^ (t.val + 6 * j) * s) % m := by
      calc
        (b_res ^ 2 + d B ^ (t.val + 6 * j) * s) % m
            = (b_res ^ 2 % m + (d B ^ (t.val + 6 * j) * s) % m) % m := by
              rw [Nat.add_mod]
        _ = (((b0_nat * d B ^ (3 * j)) % m) ^ 2 % m +
              (d B ^ (t.val + 6 * j) * s) % m) % m := by
              have : b_res ^ 2 % m = ((b0_nat * d B ^ (3 * j)) % m) ^ 2 % m := by
                have h1 : b_res % m = (b0_nat * d B ^ (3 * j)) % m := hscale
                exact (pow_mod_congr h1 2).trans
                  (pow_mod_congr (Nat.mod_mod _ _) 2).symm
              rw [this]
        _ = (((b0_nat * d B ^ (3 * j)) % m) ^ 2 +
              d B ^ (t.val + 6 * j) * s) % m := by
              rw [← Nat.add_mod]
    have hEq :
        (etaResidue B (t.val + 6 * j) m s ^ twistK B *
            (b_res ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m
          = (d B ^ (6 * j) * localTarget B t s b0_nat) % m := by
      have hmul :
          (etaResidue B (t.val + 6 * j) m s ^ twistK B *
              (b_res ^ 2 + d B ^ (t.val + 6 * j) * s)) % m
            = (etaResidue B (t.val + 6 * j) m s ^ twistK B *
                (((b0_nat * d B ^ (3 * j)) % m) ^ 2
                  + d B ^ (t.val + 6 * j) * s)) % m := by
        calc
          _ = (etaResidue B (t.val + 6 * j) m s ^ twistK B % m *
                ((b_res ^ 2 + d B ^ (t.val + 6 * j) * s) % m)) % m := by
              rw [Nat.mul_mod]
          _ = (etaResidue B (t.val + 6 * j) m s ^ twistK B % m *
                ((((b0_nat * d B ^ (3 * j)) % m) ^ 2
                  + d B ^ (t.val + 6 * j) * s) % m)) % m := by
              rw [hb2]
          _ = _ := by rw [← Nat.mul_mod]
      calc
        (etaResidue B (t.val + 6 * j) m s ^ twistK B *
            (b_res ^ 2 + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m
            = ((etaResidue B (t.val + 6 * j) m s ^ twistK B *
                (b_res ^ 2 + d B ^ (t.val + 6 * j) * s)) % m *
                ((m + 1) / 2 % m)) % m := by
              rw [Nat.mul_mod]
        _ = ((etaResidue B (t.val + 6 * j) m s ^ twistK B *
                (((b0_nat * d B ^ (3 * j)) % m) ^ 2
                  + d B ^ (t.val + 6 * j) * s)) % m *
                ((m + 1) / 2 % m)) % m := by rw [hmul]
        _ = (etaResidue B (t.val + 6 * j) m s ^ twistK B *
                (((b0_nat * d B ^ (3 * j)) % m) ^ 2
                  + d B ^ (t.val + 6 * j) * s) * ((m + 1) / 2)) % m := by
              rw [← Nat.mul_mod]
        _ = (d B ^ (6 * j) * localTarget B t s b0_nat) % m := hp
    have hcube' : IsCube m ((d B ^ (6 * j) * localTarget B t s b0_nat) % m) :=
      hEq ▸ hcube
    have hcube'' : IsCube m
        ((periodCubeRoot B j ^ 3 * localTarget B t s b0_nat) % m) := by
      simpa [d_six_j_is_cube B j] using hcube'
    have hinner := isCube_of_mul_cube (u := periodCubeRoot B j)
      (target := localTarget B t s b0_nat) u_cop hm1 hcube''
    rw [value_eq_localTarget]
    have hmod :
        localTarget B t s b0_nat % m = localTarget B t s b0_nat := by
      simp only [localTarget]
      change (_ % m) % m = _ % m
      exact Nat.mod_mod _ _
    rwa [← hmod]
  exact ⟨transport (root B) (by simpa [b_res] using cube1),
    transport (m - root B) (by simpa [b_res] using cube2)⟩

/-- **L3 headline.** Under the cubic gap, `d^x + b^4 = c^3` has no solution
with odd `x` and even `c`. -/
theorem no_even_c_cubic (B : Base) (gap : CubicGap B)
    (b c : Int) (x : Nat) (hx : x % 2 = 1) (hc : c % 2 = 0)
    (eqn : (d B : Int) ^ x + b ^ 4 = c ^ 3) : False := by
  obtain ⟨t, j, hxj⟩ := odd_exponent_mod_twelve hx
  have hb_odd := b_odd_of_even_c (B := B) hc eqn
  obtain ⟨beta, hid⟩ := gap.oriented_cube b c x hx hc eqn
  have ht_full : (x - 1) / 2 = t.val + 6 * j := by omega
  rw [ht_full] at hid
  obtain ⟨b0, h1, h2⟩ :=
    local_cubes_of_identity (B := B) (t := t) (j := j) (b := b) hb_odd hid
  exact (no_local_cubes B t b0) ⟨h1, h2⟩

theorem no_even_c_cubic_167 (gap : CubicGap .d167)
    (b c : Int) (x : Nat) (hx : x % 2 = 1) (hc : c % 2 = 0)
    (eqn : (167 : Int) ^ x + b ^ 4 = c ^ 3) : False :=
  no_even_c_cubic .d167 gap b c x hx hc eqn

theorem no_even_c_cubic_2471 (gap : CubicGap .d2471)
    (b c : Int) (x : Nat) (hx : x % 2 = 1) (hc : c % 2 = 0)
    (eqn : (2471 : Int) ^ x + b ^ 4 = c ^ 3) : False :=
  no_even_c_cubic .d2471 gap b c x hx hc eqn

end Beal.CubicPeriod

#print axioms Beal.CubicPeriod.odd_exponent_mod_twelve
#print axioms Beal.CubicPeriod.usesEta_period
#print axioms Beal.CubicPeriod.no_even_c_cubic
#print axioms Beal.CubicPeriod.no_even_c_cubic_167
#print axioms Beal.CubicPeriod.no_even_c_cubic_2471
