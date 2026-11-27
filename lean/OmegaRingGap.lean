import OmegaRing
import OmegaRingDedekind
import OmegaRingGamma
import OmegaRingEta
import OmegaRingPrincipalizer
import Mathlib.Tactic

/-!
# L2f: assemble `DedekindGap` and drop the gap packaging

Packages L2c–L2e into concrete `DedekindGap` certificates for both project
bases. The only remaining external assumption is L2e's
`ClassGroupOrderHypothesis` (Mathlib `ClassGroup` orders 11 / 62).

From that hypothesis one obtains:
* an `IdealFrontDoor` (signed twist for odd `x` with `gcd(b,d)=1`);
* cubic exclusions `no_integral_twist*_of_classGroupOrder` that take only
  the Diophantine equation — no `IdealAPI` or `DedekindGap` argument.
-/

open Beal
open OmegaRing
open IdealDescent
open QuadraticBridge
open TwistIdentity
open OmegaRingGamma
open OmegaRingEta
open OmegaRingPrincipalizer

namespace Beal.OmegaRingGap

/-! ## Assembled Dedekind gaps -/

/-- `DedekindGap` for `d = 167` from L2c–L2e under `classGroupOrder_167`. -/
noncomputable def dedekindGap167 (hh : classGroupOrder_167) :
    DedekindGap 167 11 42 eta167 idealAPI167 where
  gamma_perfect_power := gamma_perfect_power_idealAPI167
  P := P167
  eta_is_P_pow := P167_pow
  principalizer := principalizer_idealAPI167 hh

set_option maxRecDepth 4096 in
/-- `DedekindGap` for `d = 2471` from L2c–L2e under `classGroupOrder_2471`. -/
noncomputable def dedekindGap2471 (hh : classGroupOrder_2471) :
    DedekindGap 2471 31 618 eta2471 idealAPI2471 where
  gamma_perfect_power := gamma_perfect_power_idealAPI2471
  P := P2471
  eta_is_P_pow := P2471_pow
  principalizer := principalizer_idealAPI2471 hh

/-! ## Front doors (ClassGroup-order hyp only) -/

/-- `IdealFrontDoor` at 167 under the ClassGroup-order hypothesis. -/
noncomputable def frontDoor167_of_classGroupOrder (hh : classGroupOrder_167) :
    IdealFrontDoor 167 11 42 eta167 :=
  frontDoor167_mathlib (dedekindGap167 hh)

/-- `IdealFrontDoor` at 2471 under the ClassGroup-order hypothesis. -/
noncomputable def frontDoor2471_of_classGroupOrder (hh : classGroupOrder_2471) :
    IdealFrontDoor 2471 31 618 eta2471 :=
  frontDoor2471_mathlib (dedekindGap2471 hh)

/-! ## Signed / unsigned twist for odd `x` -/

/-- Unsigned twist identity at 167 for odd `x` with `gcd(b,167)=1`. -/
theorem twist_identity167 (hh : classGroupOrder_167)
    (b c : Int) (x : Nat) (hx : x % 2 = 1)
    (hbd : Int.gcd b (167 : Int) = 1)
    (eqn : (167 : Int) ^ x + b ^ 4 = c ^ 11) :
    ∃ (beta : Element) (k : Nat),
      k < 11 ∧
      pow 42 beta 11 =
        mul 42 (pow 42 eta167 k) (gammaOf ((167 : Int) ^ ((x - 1) / 2)) b) :=
  twist_identity_of_front_door (frontDoor167_of_classGroupOrder hh) b c x hx hbd eqn

/-- Unsigned twist identity at 2471 for odd `x` with `gcd(b,2471)=1`. -/
theorem twist_identity2471 (hh : classGroupOrder_2471)
    (b c : Int) (x : Nat) (hx : x % 2 = 1)
    (hbd : Int.gcd b (2471 : Int) = 1)
    (eqn : (2471 : Int) ^ x + b ^ 4 = c ^ 31) :
    ∃ (beta : Element) (k : Nat),
      k < 31 ∧
      pow 618 beta 31 =
        mul 618 (pow 618 eta2471 k) (gammaOf ((2471 : Int) ^ ((x - 1) / 2)) b) :=
  twist_identity_of_front_door (frontDoor2471_of_classGroupOrder hh) b c x hx hbd eqn

/-! ## Cubic exclusions (equation + ClassGroup-order hyp only) -/

/-- Cubic exclusion at 167: no `api`, no `DedekindGap` — only the equation
and the L2e ClassGroup-order hypothesis. Coprimality is derived (L2a). -/
theorem no_integral_twist167_of_classGroupOrder (hh : classGroupOrder_167)
    (b c : Int) (eqn : (167 : Int) ^ 3 + b ^ 4 = c ^ 11) : False :=
  no_integral_twist167_of_mathlib_gap (dedekindGap167 hh) b c eqn

/-- Cubic exclusion at 2471: no `api`, no `DedekindGap` — only the equation
and the L2e ClassGroup-order hypothesis. Coprimality is derived (L2a). -/
theorem no_integral_twist2471_of_classGroupOrder (hh : classGroupOrder_2471)
    (b c : Int) (eqn : (2471 : Int) ^ 3 + b ^ 4 = c ^ 31) : False :=
  no_integral_twist2471_of_mathlib_gap (dedekindGap2471 hh) b c eqn

end Beal.OmegaRingGap

#print axioms Beal.OmegaRingGap.dedekindGap167
#print axioms Beal.OmegaRingGap.dedekindGap2471
#print axioms Beal.OmegaRingGap.twist_identity167
#print axioms Beal.OmegaRingGap.twist_identity2471
#print axioms Beal.OmegaRingGap.no_integral_twist167_of_classGroupOrder
#print axioms Beal.OmegaRingGap.no_integral_twist2471_of_classGroupOrder
