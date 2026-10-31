import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Median certificate: `lem:median-certificate`
Target: Lean 4.19.0 / mathlib 4.19.0.
Adapted from the existing local Lemma12.lean proof of the same lemma.

All definitions come first, followed by the full main statement (Lemma12).
Supporting proofs then establish parameters, the lattice wave, convexity,
and the four geometric cases. The final theorem `median_certificate`
assembles them. Search for CASE 1, CASE 2, CASE 3, CASE 4.

Arithmetic is exact. Rational enclosures remain for root isolation and
transcendental endpoint inequalities. Convexity uses the symbolic second
derivative and only proves its sign, rather than an approximate derivative.
No sorry, custom axioms, native_decide, or floating-point computation.
Verification status is reported separately in the accompanying verifier log.
-/

namespace Clustering
noncomputable section

/-! ===================== ALL DEFINITIONS ===================== -/

def pos (x : ℝ) : ℝ := max x 0

def K (α r s c : ℝ) : ℝ :=
  (pos (r + c - α * r) + pos (s + c - α * s)
    - pos (α * r - s) - pos (α * s - r)) / 2

def beta (α : ℝ) : ℝ := α - 1

def gamma (α : ℝ) : ℝ := beta α - 1 / (2 * beta α)

def rho (α : ℝ) : ℝ :=
  -(1 / (2 * Real.log α)) *
    Real.log (4 * (beta α)^2 * α / (α^2 + 1))

def tau (L z : ℝ) : ℝ :=
  1 - (2 / L) * Metric.infDist z
    (Set.range (fun n : ℤ => (2 * L) * (n : ℝ)))

def IsAlpha (α : ℝ) : Prop :=
  (171954 : ℝ) / 100000 < α ∧ α < (171955 : ℝ) / 100000 ∧
  Real.sqrt (α^2 + 1) + 1 - α^2 = Real.sqrt α * gamma α

def boundRHS (α r s c : ℝ) : ℝ :=
  -(Real.exp (-(rho α) * |Real.log (r / s)|) /
      (4 * beta α * Real.sqrt (r * s))) * (r^2 + s^2 - c^2)
    - gamma α * Real.sqrt (r * s) * tau (Real.log α) (Real.log (r / s))

/-! ===================== AUXILIARY DEFINITIONS ===================== -/

def rootFn (a : ℝ) : ℝ :=
  Real.sqrt (a^2 + 1) + 1 - a^2 - Real.sqrt a * gamma a

def expSum {n : ℕ} (w a : Fin n → ℝ) (z : ℝ) : ℝ := ∑ i, w i * Real.exp (a i * z)

def rates (p : ℝ) : Fin 5 → ℝ := ![1-p, -(1+p), p, 1/2, -(1/2)]

def weightsLo (b : ℝ) : Fin 5 → ℝ := ![1/(4*b), 1/(4*b), b, -b, -b]

def weightsHi (b : ℝ) : Fin 5 → ℝ := ![1/(4*b), 1/(4*b), b, -(2*b+1)/2, (1-b)/2]

def hLo (b p z : ℝ) := expSum (weightsLo b) (rates p) z

def hHi (b p z : ℝ) := expSum (weightsHi b) (rates p) z

def radialH (a z : ℝ) := if z ≤ Real.log a then hLo (beta a) (rho a) z else hHi (beta a) (rho a) z

def correction (b p : ℝ) := expSum ![-3*b/4,b/2] ![p,1/2]

def potential (b q u c : ℝ) : ℝ :=
  (pos (c-b*q^2)+pos (c-b)-(b+1)*q^2+1-pos (b+1-q^2))/(2*q) +
  (q^4+1-c^2)/(4*b*u*q^2)

def envelope (b q u : ℝ) : ℝ :=
  (q^4+1)/(4*b*u*q^2)+b*u-
  (b*(q^2+1)+(b+1)*q^2-1+pos (b+1-q^2))/(2*q)

/-! ===================== MAIN STATEMENT ===================== -/

def Lemma12 : Prop :=
  (∃! α : ℝ, IsAlpha α) ∧
  ∀ α : ℝ, IsAlpha α →
    ∀ r s c : ℝ, 0 < r → 0 < s → |r - s| ≤ c → c ≤ r + s →
      K α r s c ≤ boundRHS α r s c



















-- The full original statement, proved by `lemma12` at the end of this file.



/-! ===================== PARAMETER PROOFS ===================== -/
theorem gamma_pos_of_lower_bound {a : ℝ} (ha : (171954 : ℝ) / 100000 < a) :
    0 < gamma a := by
  have hb : 0 < a - 1 := by linarith
  unfold gamma beta
  apply sub_pos.mpr
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (a - 1))).2
  nlinarith

theorem gamma_strictMono {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    gamma a < gamma b := by
  have hi := one_div_lt_one_div_of_lt
    (show 0 < 2 * (a - 1) by linarith)
    (show 2 * (a - 1) < 2 * (b - 1) by linarith)
  unfold gamma beta
  linarith

theorem root_unique {a b : ℝ} (ha : IsAlpha a) (hb : IsAlpha b) : a = b := by
  have no_increase : ∀ x y : ℝ, IsAlpha x → IsAlpha y → x < y → False := by
    intro x y hx hy hxy
    have hx1 : 1 < x := by linarith [hx.1]
    have hy1 : 1 < y := by linarith
    have hsx : 0 ≤ Real.sqrt (x^2 + 1) := Real.sqrt_nonneg _
    have hsy : 0 ≤ Real.sqrt (y^2 + 1) := Real.sqrt_nonneg _
    have hsqx := Real.sq_sqrt (show 0 ≤ x^2 + 1 by positivity)
    have hsqy := Real.sq_sqrt (show 0 ≤ y^2 + 1 by positivity)
    have hsum : 1 < Real.sqrt (x^2 + 1) + Real.sqrt (y^2 + 1) := by
      have : 1 < Real.sqrt (x^2 + 1) := by nlinarith
      linarith
    have hdiff : 0 < Real.sqrt (y^2 + 1) - Real.sqrt (x^2 + 1) := by
      apply sub_pos.mpr
      apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith
    have hlhs : Real.sqrt (y^2 + 1) + 1 - y^2 <
        Real.sqrt (x^2 + 1) + 1 - x^2 := by
      nlinarith [mul_pos hdiff (sub_pos.mpr hsum)]
    have hgx := gamma_pos_of_lower_bound hx.1
    have hgxy := gamma_strictMono hx1 hxy
    have hsyx := Real.sqrt_lt_sqrt (show 0 ≤ x by linarith) hxy
    have hrhs : Real.sqrt x * gamma x < Real.sqrt y * gamma y := by
      have hsyp : 0 < Real.sqrt y := Real.sqrt_pos.2 (by linarith)
      nlinarith [mul_pos (sub_pos.mpr hsyx) hgx,
        mul_pos hsyp (sub_pos.mpr hgxy)]
    linarith [hx.2.2, hy.2.2]
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_increase a b ha hb hab)
  · exact hab
  · exact False.elim (no_increase b a hb ha hab)




theorem rootFn_lower_pos : 0 < rootFn ((171954 : ℝ) / 100000) := by
  have h1 := Real.sq_sqrt (show 0 ≤ ((171954 : ℝ) / 100000)^2 + 1 by norm_num)
  have h2 := Real.sq_sqrt (show 0 ≤ (171954 : ℝ) / 100000 by norm_num)
  have hn1 := Real.sqrt_nonneg (((171954 : ℝ) / 100000)^2 + 1)
  have hn2 := Real.sqrt_nonneg ((171954 : ℝ) / 100000)
  have hl : (198917515 : ℝ) / 100000000 <
      Real.sqrt (((171954 : ℝ) / 100000)^2 + 1) := by nlinarith
  have hu : Real.sqrt ((171954 : ℝ) / 100000) <
      (131131233 : ℝ) / 100000000 := by nlinarith
  norm_num [rootFn, gamma, beta] at *
  nlinarith

theorem rootFn_upper_neg : rootFn ((171955 : ℝ) / 100000) < 0 := by
  have h1 := Real.sq_sqrt (show 0 ≤ ((171955 : ℝ) / 100000)^2 + 1 by norm_num)
  have h2 := Real.sq_sqrt (show 0 ≤ (171955 : ℝ) / 100000 by norm_num)
  have hn1 := Real.sqrt_nonneg (((171955 : ℝ) / 100000)^2 + 1)
  have hn2 := Real.sqrt_nonneg ((171955 : ℝ) / 100000)
  have hu : Real.sqrt (((171955 : ℝ) / 100000)^2 + 1) <
      (198918381 : ℝ) / 100000000 := by nlinarith
  have hl : (131131613 : ℝ) / 100000000 <
      Real.sqrt ((171955 : ℝ) / 100000) := by nlinarith
  norm_num [rootFn, gamma, beta] at *
  nlinarith

theorem alpha_exists_unique : ∃! a : ℝ, IsAlpha a := by
  let lo : ℝ := 171954 / 100000
  let hi : ℝ := 171955 / 100000
  have hl : 0 < rootFn lo := rootFn_lower_pos
  have hh : rootFn hi < 0 := rootFn_upper_neg
  have hcont : ContinuousOn rootFn (Set.Icc lo hi) := by
    apply continuousOn_of_forall_continuousAt
    intro a ha
    have hn : 2 * (a - 1) ≠ 0 := by
      dsimp [lo] at ha
      have : 0 < 2 * (a - 1) := by linarith [ha.1]
      exact ne_of_gt this
    unfold rootFn gamma beta
    fun_prop (disch := assumption)
  obtain ⟨a, ha, hz⟩ := intermediate_value_Icc'
    (show lo ≤ hi by norm_num [lo, hi]) hcont ⟨hh.le, hl.le⟩
  have hal : lo < a := by
    by_contra h
    have heq : a = lo := by linarith [ha.1]
    rw [heq] at hz
    linarith
  have hah : a < hi := by
    by_contra h
    have heq : a = hi := by linarith [ha.2]
    rw [heq] at hz
    linarith
  have ha' : IsAlpha a := by
    refine ⟨hal, hah, ?_⟩
    unfold rootFn at hz
    linarith
  exact ⟨a, ha', fun b hb => root_unique hb ha'⟩

@[simp] theorem tau_zero (L : ℝ) : tau L 0 = 1 := by
  have hm : (0 : ℝ) ∈ Set.range (fun n : ℤ => (2 * L) * (n : ℝ)) := by
    exact ⟨0, by simp⟩
  simp [tau, Metric.infDist_zero_of_mem hm]

-- The elementary inequality behind the completed-square arguments.
theorem quadratic_bound (a b x : ℝ) (hb : 0 < b) :
    a * x - b * x^2 ≤ a^2 / (4 * b) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * b)).2
  nlinarith [sq_nonneg (2 * b * x - a)]

theorem positive_part_bound (t c : ℝ) (ht : 0 < t) :
    pos (c - t) ≤ c^2 / (4 * t) := by
  unfold pos
  apply max_le
  · apply (le_div_iff₀ (by positivity : 0 < 4 * t)).2
    nlinarith [sq_nonneg (c - 2 * t)]
  · positivity

-- Equal-radius algebra, valid for EVERY α > 1 and every real c.
theorem equal_radius_algebra (α r c : ℝ) (hα : 1 < α) (hr : 0 < r) :
    K α r r c ≤
      -(1 / (4 * (α - 1) * r)) * (r^2 + r^2 - c^2)
        - ((α - 1) - 1 / (2 * (α - 1))) * r := by
  have hb : 0 < α - 1 := sub_pos.mpr hα
  have ht : 0 < (α - 1) * r := mul_pos hb hr
  have hpos : pos (α * r - r) = (α - 1) * r := by
    unfold pos
    rw [show α * r - r = (α - 1) * r by ring, max_eq_left ht.le]
  have hk : K α r r c = pos (c - (α - 1) * r) - (α - 1) * r := by
    unfold K
    rw [hpos, show r + c - α * r = c - (α - 1) * r by ring]
    ring
  rw [hk]
  have h := positive_part_bound ((α - 1) * r) c ht
  have heq :
      -(1 / (4 * (α - 1) * r)) * (r^2 + r^2 - c^2)
        - ((α - 1) - 1 / (2 * (α - 1))) * r =
      c^2 / (4 * ((α - 1) * r)) - (α - 1) * r := by
    field_simp [ne_of_gt hb, ne_of_gt hr]
    ring
  rw [heq]
  linarith

-- Actual inequality (11) in the case r = s, with the original RHS.
theorem lemma12_equal_radii (α r c : ℝ) (hα : 1 < α) (hr : 0 < r) :
    K α r r c ≤ boundRHS α r r c := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  simpa [boundRHS, div_self hr0, Real.sqrt_mul_self hr.le,
    gamma, beta] using equal_radius_algebra α r c hα hr


theorem exp_bound_0 : ((859721 : ℝ) / 500000) < Real.exp ((271 : ℝ) / 500) ∧
    Real.exp ((271 : ℝ) / 500) < ((1719443 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((271 : ℝ) / 500)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_1 : ((859807 : ℝ) / 500000) < Real.exp ((5421 : ℝ) / 10000) ∧
    Real.exp ((5421 : ℝ) / 10000) < ((343923 : ℝ) / 200000) := by
  have h := Real.exp_bound (x := ((5421 : ℝ) / 10000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_2 : ((900173 : ℝ) / 1000000) < Real.exp ((-525837 : ℝ) / 5000000) ∧
    Real.exp ((-525837 : ℝ) / 5000000) < ((450087 : ℝ) / 500000) := by
  have h := Real.exp_bound (x := ((-525837 : ℝ) / 5000000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_3 : ((56201 : ℝ) / 62500) < Real.exp ((-13279 : ℝ) / 125000) ∧
    Real.exp ((-13279 : ℝ) / 125000) < ((899217 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((-13279 : ℝ) / 125000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_8 : ((608263 : ℝ) / 500000) < Real.exp ((49 : ℝ) / 250) ∧
    Real.exp ((49 : ℝ) / 250) < ((1216527 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((49 : ℝ) / 250)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_9 : ((2718281 : ℝ) / 1000000) < Real.exp ((1 : ℝ) / 1) ∧
    Real.exp ((1 : ℝ) / 1) < ((1359141 : ℝ) / 500000) := by
  have h := Real.exp_bound (x := ((1 : ℝ) / 1)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_10 : ((367879 : ℝ) / 1000000) < Real.exp ((-1 : ℝ) / 1) ∧
    Real.exp ((-1 : ℝ) / 1) < ((9197 : ℝ) / 25000) := by
  have h := Real.exp_bound (x := ((-1 : ℝ) / 1)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_11 : ((1968457 : ℝ) / 1000000) < Real.exp ((2709 : ℝ) / 4000) ∧
    Real.exp ((2709 : ℝ) / 4000) < ((984229 : ℝ) / 500000) := by
  have h := Real.exp_bound (x := ((2709 : ℝ) / 4000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_12 : ((219611 : ℝ) / 500000) < Real.exp ((-3291 : ℝ) / 4000) ∧
    Real.exp ((-3291 : ℝ) / 4000) < ((439223 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((-3291 : ℝ) / 4000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_13 : ((1158353 : ℝ) / 1000000) < Real.exp ((147 : ℝ) / 1000) ∧
    Real.exp ((147 : ℝ) / 1000) < ((579177 : ℝ) / 500000) := by
  have h := Real.exp_bound (x := ((147 : ℝ) / 1000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_14 : ((2117 : ℝ) / 1000) < Real.exp ((3 : ℝ) / 4) ∧
    Real.exp ((3 : ℝ) / 4) < ((2117001 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((3 : ℝ) / 4)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_15 : ((236183 : ℝ) / 500000) < Real.exp ((-3 : ℝ) / 4) ∧
    Real.exp ((-3 : ℝ) / 4) < ((472367 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((-3 : ℝ) / 4)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem exp_bound_17 : ((154187 : ℝ) / 62500) < Real.exp ((903 : ℝ) / 1000) ∧
    Real.exp ((903 : ℝ) / 1000) < ((2466993 : ℝ) / 1000000) := by
  have h := Real.exp_bound (x := ((903 : ℝ) / 1000)) (n := 16) (by norm_num [abs_div]) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_div] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem basic_parameter_bounds {a : ℝ} (ha : IsAlpha a) :
    (7195 : ℝ)/10000 < beta a ∧ beta a < (7196 : ℝ)/10000 ∧
    (246 : ℝ)/10000 < gamma a ∧ gamma a < (247 : ℝ)/10000 ∧
    (542 : ℝ)/1000 < Real.log a ∧ Real.log a < (5421 : ℝ)/10000 := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hgl := gamma_strictMono (by norm_num : (1 : ℝ) < 171954/100000) ha.1
  have hgu := gamma_strictMono (show 1 < a by linarith [ha.1]) ha.2.1
  have hgl' : (246 : ℝ)/10000 < gamma a := by
    norm_num [gamma, beta] at hgl ⊢
    linarith
  have hgu' : gamma a < (247 : ℝ)/10000 := by
    norm_num [gamma, beta] at hgu ⊢
    linarith
  have hl : (542 : ℝ)/1000 < Real.log a := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log ha0]
    linarith [exp_bound_0.2, ha.1]
  have hu : Real.log a < (5421 : ℝ)/10000 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log ha0]
    linarith [exp_bound_1.1, ha.2.1]
  exact ⟨by dsimp [beta]; linarith [ha.1],
    by dsimp [beta]; linarith [ha.2.1], hgl', hgu', hl, hu⟩

theorem rho_bounds {a : ℝ} (ha : IsAlpha a) :
    (97 : ℝ)/1000 < rho a ∧ rho a < (98 : ℝ)/1000 := by
  have hp := basic_parameter_bounds ha
  have hb0 : 0 < beta a := by linarith [hp.1]
  have ha0 : 0 < a := by linarith [ha.1]
  have hL : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  let R := 4 * (beta a)^2 * a / (a^2 + 1)
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hRl : (8999 : ℝ)/10000 < R := by
    calc
      (8999 : ℝ)/10000 < 4 * ((71954 : ℝ)/100000)^2 * (171954/100000) /
        ((171955/100000)^2 + 1) := by norm_num
      _ ≤ R := by
        dsimp [R, beta]
        gcongr <;> linarith [ha.1, ha.2.1]
  have hRu : R < (9001 : ℝ)/10000 := by
    calc
      R ≤ 4 * ((71955 : ℝ)/100000)^2 * (171955/100000) /
        ((171954/100000)^2 + 1) := by
          dsimp [R, beta]
          gcongr <;> linarith [ha.1, ha.2.1]
      _ < (9001 : ℝ)/10000 := by norm_num
  have hlogl : -(106232 : ℝ)/1000000 < Real.log R := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hR0]
    linarith [exp_bound_3.2]
  have hlogu : Real.log R < -(1051674 : ℝ)/10000000 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hR0]
    linarith [exp_bound_2.1]
  have heq : rho a = -Real.log R / (2 * Real.log a) := by dsimp [rho, R]; ring
  rw [heq]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log a)).2
    linarith [hp.2.2.2.2.2]
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log a)).2
    linarith [hp.2.2.2.2.1]

theorem tau_le_one {L z : ℝ} (hL : 0 < L) : tau L z ≤ 1 := by
  unfold tau
  have h : 0 ≤ (2 / L) * Metric.infDist z
      (Set.range (fun n : ℤ => (2 * L) * (n : ℝ))) :=
    mul_nonneg (by positivity) Metric.infDist_nonneg
  linarith

theorem tau_first {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) (hzL : z ≤ L) :
    tau L z = 1 - 2 * z / L := by
  have hdist : Metric.infDist z
      (Set.range (fun n : ℤ => (2 * L) * (n : ℝ))) = z := by
    apply le_antisymm
    · have h := Metric.infDist_le_dist_of_mem
        (x := z) (show (0 : ℝ) ∈ Set.range (fun n : ℤ => (2 * L) * (n : ℝ))
          from ⟨0, by simp⟩)
      simpa [Real.dist_eq, abs_of_nonneg hz] using h
    · apply (Metric.le_infDist (Set.range_nonempty _)).2
      rintro _ ⟨n, rfl⟩
      rw [Real.dist_eq]
      by_cases hn : n ≤ 0
      · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        have := le_abs_self (z - 2 * L * (n : ℝ))
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hL.le hn']
      · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        have := neg_le_abs (z - 2 * L * (n : ℝ))
        nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hn')]
  unfold tau
  rw [hdist]
  ring

theorem tau_second {L z : ℝ} (hL : 0 < L) (hz : L ≤ z) (hzL : z ≤ 2 * L) :
    tau L z = -3 + 2 * z / L := by
  have hdist : Metric.infDist z
      (Set.range (fun n : ℤ => (2 * L) * (n : ℝ))) = 2 * L - z := by
    apply le_antisymm
    · have h := Metric.infDist_le_dist_of_mem
        (x := z) (show 2 * L ∈ Set.range (fun n : ℤ => (2 * L) * (n : ℝ))
          from ⟨1, by simp⟩)
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hzL)] using h
    · apply (Metric.le_infDist (Set.range_nonempty _)).2
      rintro _ ⟨n, rfl⟩
      rw [Real.dist_eq]
      by_cases hn : n ≤ 0
      · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        have := le_abs_self (z - 2 * L * (n : ℝ))
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hL.le hn']
      · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        have := neg_le_abs (z - 2 * L * (n : ℝ))
        nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hn')]
  unfold tau
  rw [hdist]
  field_simp
  ring

theorem tau_even (L z : ℝ) : tau L (-z) = tau L z := by
  let S := Set.range (fun n : ℤ => (2 * L) * (n : ℝ))
  have hS : Neg.neg '' S = S := by
    ext y
    constructor
    · rintro ⟨v, ⟨n, rfl⟩, rfl⟩
      exact ⟨-n, by push_cast; ring⟩
    · rintro ⟨n, rfl⟩
      refine ⟨(2 * L) * ((-n : ℤ) : ℝ), ⟨-n, rfl⟩, ?_⟩
      push_cast
      ring
  have h := Metric.infDist_image (x := z) (t := S) (isometry_neg : Isometry (Neg.neg : ℝ → ℝ))
  rw [hS] at h
  unfold tau
  rw [h]


/-! ===================== SYMBOLIC DERIVATIVES AND CONVEXITY ===================== -/

theorem expSum_hasDeriv {n : ℕ} (w a : Fin n → ℝ) (z : ℝ) :
    HasDerivAt (expSum w a) (expSum (fun i => w i * a i) a z) z := by
  have hterm (i : Fin n) :
      HasDerivAt (fun x : ℝ => w i * Real.exp (a i * x))
        (w i * a i * Real.exp (a i * z)) z := by
    simpa only [Function.comp_def, mul_one, mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_exp (a i * z)).comp z
        ((hasDerivAt_id z).const_mul (a i))).const_mul (w i))
  have hsum : (∑ i : Fin n, fun x : ℝ => w i * Real.exp (a i * x)) =
      expSum w a := by
    funext x
    simp only [Finset.sum_apply, expSum]
  rw [← hsum]
  exact HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)

theorem expSum_convex {n : ℕ} (w a : Fin n → ℝ) {D : Set ℝ}
    (hD : Convex ℝ D)
    (hpos : ∀ z ∈ D, 0 ≤ expSum (fun i => w i * a i * a i) a z) :
    ConvexOn ℝ D (expSum w a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg hD
    (continuousOn_of_forall_continuousAt (fun z _ => (expSum_hasDeriv w a z).continuousAt))
    (fun z _ => (expSum_hasDeriv w a z).hasDerivWithinAt)
    (fun z _ => (expSum_hasDeriv (fun i => w i * a i) a z).hasDerivWithinAt)
  exact fun z hz => hpos z (interior_subset hz)







lemma hLo_formula (b p z : ℝ) :
    hLo b p z = (Real.exp ((1-p)*z) + Real.exp (-(1+p)*z))/(4*b) +
      b*Real.exp (p*z) - b*(Real.exp (z/2) + Real.exp (-z/2)) := by
  simp [hLo, expSum, weightsLo, rates, Fin.sum_univ_succ]
  ring_nf
lemma hHi_formula (b p z : ℝ) :
    hHi b p z = (Real.exp ((1-p)*z) + Real.exp (-(1+p)*z))/(4*b) +
      b*Real.exp (p*z) - (2*b+1)/2*Real.exp (z/2) + (1-b)/2*Real.exp (-z/2) := by
  simp [hHi, expSum, weightsHi, rates, Fin.sum_univ_succ]
  ring_nf
lemma hLo_second (b p z : ℝ) :
    expSum (fun i => weightsLo b i * rates p i * rates p i) (rates p) z =
      ((1-p)^2*Real.exp ((1-p)*z) + (1+p)^2*Real.exp (-(1+p)*z))/(4*b) +
      b*p^2*Real.exp (p*z) - b/4*(Real.exp (z/2) + Real.exp (-z/2)) := by
  simp [expSum, weightsLo, rates, Fin.sum_univ_succ]
  ring_nf
lemma hHi_second (b p z : ℝ) :
    expSum (fun i => weightsHi b i * rates p i * rates p i) (rates p) z =
      ((1-p)^2*Real.exp ((1-p)*z) + (1+p)^2*Real.exp (-(1+p)*z))/(4*b) +
      b*p^2*Real.exp (p*z) - (2*b+1)/8*Real.exp (z/2) + (1-b)/8*Real.exp (-z/2) := by
  simp [expSum, weightsHi, rates, Fin.sum_univ_succ]
  ring_nf

lemma hLo_second_nonneg {b p z : ℝ}
    (hb : 0 < b) (hbu : b ≤ 72/100) (hp : 0 ≤ p) (hpu : p ≤ 1/10)
    (hz : 0 ≤ z) (hzu : z ≤ 543/1000) :
    0 ≤ expSum (fun i => weightsLo b i * rates p i * rates p i) (rates p) z := by
  rw [hLo_second]
  -- AM-GM in squared form: this is an exact symbolic inequality.
  have hsq1 : Real.exp ((1-p)*z/2)^2 = Real.exp ((1-p)*z) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsq2 : Real.exp (-(1+p)*z/2)^2 = Real.exp (-(1+p)*z) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp ((1-p)*z/2)*Real.exp (-(1+p)*z/2) =
      Real.exp (-p*z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid :
      (1-p)^2*Real.exp ((1-p)*z) + (1+p)^2*Real.exp (-(1+p)*z) -
        2*(1-p^2)*Real.exp (-p*z) =
      ((1-p)*Real.exp ((1-p)*z/2) - (1+p)*Real.exp (-(1+p)*z/2))^2 := by
    conv_rhs => rw [sub_sq, mul_pow, mul_pow, hsq1, hsq2]
    rw [show 2*((1-p)*Real.exp ((1-p)*z/2))*
        ((1+p)*Real.exp (-(1+p)*z/2)) =
        2*(1-p)*(1+p)*(Real.exp ((1-p)*z/2)*Real.exp (-(1+p)*z/2)) by ring,
      hprod]
    ring
  have ham : 2*(1-p^2)*Real.exp (-p*z) ≤
      (1-p)^2*Real.exp ((1-p)*z) + (1+p)^2*Real.exp (-(1+p)*z) := by
    have hh := sq_nonneg
      ((1-p)*Real.exp ((1-p)*z/2) - (1+p)*Real.exp (-(1+p)*z/2))
    rw [← hid] at hh
    linarith
  -- Only coarse rational inequalities and exp(t) >= 1+t are needed.
  have hpz : p*z ≤ 3/50 := by
    calc
      p*z ≤ (1/10)*(3/5) := by gcongr <;> linarith
      _ = _ := by norm_num
  have he : (47:ℝ)/50 ≤ Real.exp (-p*z) := by
    linarith [Real.add_one_le_exp (-p*z)]
  have hp2 : (99:ℝ)/100 ≤ 1-p^2 := by nlinarith
  have hmain : (9:ℝ)/5 ≤
      (1-p)^2*Real.exp ((1-p)*z) + (1+p)^2*Real.exp (-(1+p)*z) := by
    have hm : (99:ℝ)/100*(47/50) ≤ (1-p^2)*Real.exp (-p*z) := by
      gcongr
    linarith
  -- exp(z/2) <= 2 follows from exp(t) <= 1/(1-t), t <= 1/2.
  have hep : Real.exp (z/2) ≤ 2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (show 0 ≤ z/2 by linarith) (show z/2 < 1 by linarith)
    have hi : 1/(1-z/2) ≤ (2:ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < 1-z/2)).2
      linarith
    exact hh.trans hi
  have hen : Real.exp (-z/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hneg : b^2*(Real.exp (z/2)+Real.exp (-z/2)) ≤ (27:ℝ)/16 := by
    calc
      _ ≤ (3/4:ℝ)^2*(2+1) := by gcongr <;> linarith
      _ = _ := by norm_num
  have hstrict : b/4*(Real.exp (z/2)+Real.exp (-z/2)) <
      ((1-p)^2*Real.exp ((1-p)*z)+(1+p)^2*Real.exp (-(1+p)*z))/(4*b) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4*b)).2
    calc
      _ = b^2*(Real.exp (z/2)+Real.exp (-z/2)) := by ring
      _ < _ := by linarith
  have hpositive : 0 <
      ((1-p)^2*Real.exp ((1-p)*z)+(1+p)^2*Real.exp (-(1+p)*z))/(4*b) +
      b*p^2*Real.exp (p*z) - b/4*(Real.exp (z/2)+Real.exp (-z/2)) := by
    have hterm : 0 ≤ b*p^2*Real.exp (p*z) := by positivity
    linarith
  exact hpositive.le

lemma hLo_convex {b p L : ℝ}
    (hb : 0 < b) (hbu : b ≤ 72/100) (hp : 0 ≤ p) (hpu : p ≤ 1/10)
    (hLu : L ≤ 543/1000) : ConvexOn ℝ (Set.Icc 0 L) (hLo b p) := by
  apply expSum_convex _ _ (convex_Icc _ _)
  intro z hz
  exact hLo_second_nonneg hb hbu hp hpu hz.1 (hz.2.trans hLu)

lemma hHi_second_nonneg {b p z : ℝ}
    (hb : 0 < b) (hbu : b ≤ 72/100) (hp : 0 ≤ p) (hpu : p ≤ 1/10)
    (hz : (542 : ℝ)/1000 ≤ z) :
    0 ≤ expSum (fun i => weightsHi b i * rates p i * rates p i) (rates p) z := by
  rw [hHi_second]
  have hz0 : 0 ≤ z := by linarith
  have hd : (3042 : ℝ)/2500 ≤ Real.exp ((1/2-p)*z) := by
    have hprod : (2/5)*((542:ℝ)/1000) ≤ (1/2-p)*z := by gcongr <;> linarith
    linarith [Real.add_one_le_exp ((1/2-p)*z)]
  have heA : ((3042 : ℝ)/2500)*Real.exp (z/2) ≤ Real.exp ((1-p)*z) := by
    rw [show (1-p)*z = (1/2-p)*z+z/2 by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hd (Real.exp_nonneg _)
  have hsq : (81 : ℝ)/100 ≤ (1-p)^2 := by nlinarith
  have hA : ((81:ℝ)/100)*((3042:ℝ)/2500)*Real.exp (z/2) ≤
      (1-p)^2*Real.exp ((1-p)*z) := by
    calc
      _ = (81/100)*((3042/2500)*Real.exp (z/2)) := by ring
      _ ≤ _ := by gcongr
  have hB : 0 ≤ (1+p)^2*Real.exp (-(1+p)*z) := by positivity
  have hmain : ((13689:ℝ)/40000)*Real.exp (z/2) ≤
      ((1-p)^2*Real.exp ((1-p)*z)+(1+p)^2*Real.exp (-(1+p)*z))/(4*b) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*b)).2
    have hmul := mul_le_mul_of_nonneg_right hbu (Real.exp_nonneg (z/2))
    nlinarith
  have hneg : (2*b+1)/8*Real.exp (z/2) ≤ ((305:ℝ)/1000)*Real.exp (z/2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    linarith
  have hpos1 : 0 ≤ b*p^2*Real.exp (p*z) := by positivity
  have hpos2 : 0 ≤ (1-b)/8*Real.exp (-z/2) := by
    apply mul_nonneg _ (Real.exp_nonneg _)
    linarith
  nlinarith [Real.exp_nonneg (z/2)]
lemma hHi_convex {b p L : ℝ}
    (hb : 0 < b) (hbu : b ≤ 72/100) (hp : 0 ≤ p) (hpu : p ≤ 1/10)
    (hLl : (542 : ℝ)/1000 ≤ L) : ConvexOn ℝ (Set.Ici L) (hHi b p) := by
  apply expSum_convex _ _ (convex_Ici _)
  intro z hz
  exact hHi_second_nonneg hb hbu hp hpu (hLl.trans hz)

lemma exp_half_sq (z : ℝ) : (Real.exp (z/2))^2 = Real.exp z := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring
lemma hLo_algebraic (b p z : ℝ) :
    hLo b p z = (Real.exp z + 1/Real.exp z)/(4*b*Real.exp (p*z)) +
      b*Real.exp (p*z) - b*(Real.exp (z/2)+1/Real.exp (z/2)) := by
  rw [hLo_formula]
  rw [show (1-p)*z = z-p*z by ring, Real.exp_sub,
    show -(1+p)*z = -z-p*z by ring, Real.exp_sub, Real.exp_neg,
    show -z/2 = -(z/2) by ring, Real.exp_neg]
  ring
lemma hHi_algebraic (b p z : ℝ) :
    hHi b p z = (Real.exp z + 1/Real.exp z)/(4*b*Real.exp (p*z)) +
      b*Real.exp (p*z) - (2*b+1)/2*Real.exp (z/2) + (1-b)/(2*Real.exp (z/2)) := by
  rw [hHi_formula]
  rw [show (1-p)*z = z-p*z by ring, Real.exp_sub,
    show -(1+p)*z = -z-p*z by ring, Real.exp_sub, Real.exp_neg,
    show -z/2 = -(z/2) by ring, Real.exp_neg]
  ring

theorem exp_rho_log_sq {a : ℝ} (ha : IsAlpha a) :
    (Real.exp (rho a * Real.log a))^2 = (a^2+1)/(4*(beta a)^2*a) := by
  have hp := basic_parameter_bounds ha
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < beta a := by linarith [hp.1]
  have hL0 : Real.log a ≠ 0 := by linarith [hp.2.2.2.2.1]
  let R := 4*(beta a)^2*a/(a^2+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have he : rho a * Real.log a + rho a * Real.log a = -Real.log R := by
    dsimp [rho, R]
    field_simp
    ring
  rw [sq, ← Real.exp_add, he, Real.exp_neg, Real.exp_log hR]
  dsimp [R]
  simp only [inv_div]

theorem hLo_at_zero {a : ℝ} : hLo (beta a) (rho a) 0 = -gamma a := by
  rw [hLo_formula]
  simp [gamma]
  ring

theorem hLo_at_log {a : ℝ} (ha : IsAlpha a) :
    hLo (beta a) (rho a) (Real.log a) = gamma a := by
  have hp := basic_parameter_bounds ha
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < beta a := by linarith [hp.1]
  let q := Real.exp (Real.log a / 2)
  let u := Real.exp (rho a * Real.log a)
  have hq0 : 0 < q := Real.exp_pos _
  have hu0 : 0 < u := Real.exp_pos _
  have hq : q^2 = a := by dsimp [q]; rw [exp_half_sq, Real.exp_log ha0]
  have hu : u^2 = (a^2+1)/(4*(beta a)^2*a) := exp_rho_log_sq ha
  have hu' : 4*(beta a)^2*a*u^2 = a^2+1 := by
    have hh := (eq_div_iff (by positivity : 4*(beta a)^2*a ≠ 0)).mp hu
    nlinarith [hh]
  have hqa : q = Real.sqrt a := by
    have hs := Real.sq_sqrt ha0.le
    have hn := Real.sqrt_nonneg a
    nlinarith
  have hprod : 2*beta a*u*q = Real.sqrt (a^2+1) := by
    have hs := Real.sq_sqrt (show 0 ≤ a^2+1 by positivity)
    have hn := Real.sqrt_nonneg (a^2+1)
    have hpq : 0 < 2*beta a*u*q := by positivity
    have hsq : (2*beta a*u*q)^2 = a^2+1 := by
      calc
        _ = 4*(beta a)^2*u^2*q^2 := by ring
        _ = a^2+1 := by rw [hq]; nlinarith [hu']
    nlinarith
  have hroot := ha.2.2
  rw [← hqa, ← hprod] at hroot
  have hb : beta a = a-1 := rfl
  have hm : (a+1/a)/(4*beta a*u) = beta a*u := by
    field_simp
    nlinarith [hu']
  have heq : (a+1/a)/(4*beta a*u)+beta a*u - beta a*(q+1/q) = gamma a := by
    rw [hm]
    apply mul_left_cancel₀ (ne_of_gt hq0)
    calc
      q * (beta a*u+beta a*u-beta a*(q+1/q)) =
        2*beta a*u*q-beta a*(q^2+1) := by field_simp <;> ring
      _ = q*gamma a := by rw [hq, hb]; rw [hb] at hroot; nlinarith only [hroot]
  rw [hLo_algebraic, Real.exp_log ha0]
  exact heq

theorem hHi_at_log {a : ℝ} (ha : IsAlpha a) :
    hHi (beta a) (rho a) (Real.log a) = gamma a := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hq := exp_half_sq (Real.log a)
  rw [Real.exp_log ha0] at hq
  have heq : hHi (beta a) (rho a) (Real.log a) = hLo (beta a) (rho a) (Real.log a) := by
    rw [hLo_algebraic, hHi_algebraic]
    have hn := Real.exp_ne_zero (Real.log a / 2)
    apply sub_eq_zero.mp
    ring_nf
    field_simp
    dsimp [beta]
    nlinarith only [hq]
  rw [heq, hLo_at_log ha]

lemma exp_double (x : ℝ) : Real.exp (2*x) = (Real.exp x)^2 := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem hHi_at_two_log {a : ℝ} (ha : IsAlpha a) :
    hHi (beta a) (rho a) (2*Real.log a) ≤ -gamma a := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb0 : 0 < beta a := by linarith [hp.1]
  have ha0 : 0 < a := by linarith [ha.1]
  have hL0 : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  have hA : Real.exp ((1-rho a)*(2*Real.log a)) ≤ (2719:ℝ)/1000 := by
    have he : Real.exp ((1-rho a)*(2*Real.log a)) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.1.le) hL0.le]
    linarith [exp_bound_9.2]
  have hB : Real.exp (-(1+rho a)*(2*Real.log a)) ≤ (368:ℝ)/1000 := by
    have he : Real.exp (-(1+rho a)*(2*Real.log a)) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ rho a by linarith) hL0.le]
    linarith [exp_bound_10.2]
  have hC : Real.exp (rho a*(2*Real.log a)) ≤ (1217:ℝ)/1000 := by
    have he : Real.exp (rho a*(2*Real.log a)) ≤ Real.exp ((49:ℝ)/250) := by
      apply Real.exp_le_exp.mpr
      have hmul : rho a*Real.log a ≤ (98/1000)*(5421/10000) := by gcongr <;> linarith
      linarith
    linarith [exp_bound_8.2]
  have hD : (171954:ℝ)/100000 ≤ Real.exp (2*Real.log a/2) := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0), Real.exp_log ha0]
    exact ha.1.le
  have hE : Real.exp (-(2*Real.log a)/2) ≤ (582:ℝ)/1000 := by
    rw [show -(2*Real.log a)/2 = -Real.log a by ring, Real.exp_neg, Real.exp_log ha0]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha0).2
    linarith [ha.1]
  rw [hHi_formula]
  calc
    _ ≤ ((2719:ℝ)/1000+368/1000)/(4*(7195/10000)) +
        (7196/10000)*(1217/1000) - (2*(7195/10000)+1)/2*(171954/100000) +
        (1-7195/10000)/2*(582/1000) := by
      gcongr <;> first | assumption | linarith [hp.1, hp.2.1]
    _ ≤ -gamma a := by linarith [hp.2.2.2.1]

theorem hHi_at_two {a : ℝ} (ha : IsAlpha a) :
    hHi (beta a) (rho a) 2 ≤ -gamma a := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb0 : 0 < beta a := by linarith [hp.1]
  have hA : Real.exp ((1-rho a)*2) ≤ (6087:ℝ)/1000 := by
    have he : Real.exp ((1-rho a)*2) ≤ Real.exp (2*((903:ℝ)/1000)) :=
      Real.exp_le_exp.mpr (by linarith [hr.1])
    rw [exp_double] at he
    nlinarith [exp_bound_17.1, exp_bound_17.2]
  have hB : Real.exp (-(1+rho a)*2) ≤ (136:ℝ)/1000 := by
    have he : Real.exp (-(1+rho a)*2) ≤ Real.exp (2*(-1)) :=
      Real.exp_le_exp.mpr (by linarith [hr.1])
    rw [exp_double] at he
    nlinarith [exp_bound_10.1, exp_bound_10.2]
  have hC : Real.exp (rho a*2) ≤ (1217:ℝ)/1000 := by
    have he := Real.exp_le_exp.mpr (show rho a*2 ≤ (49:ℝ)/250 by linarith [hr.2])
    linarith [exp_bound_8.2]
  have hD : (2718:ℝ)/1000 ≤ Real.exp (2/2) := by norm_num; linarith [exp_bound_9.1]
  have hE : Real.exp (-2/2) ≤ (368:ℝ)/1000 := by norm_num; linarith [exp_bound_10.2]
  rw [hHi_formula]
  calc
    _ ≤ ((6087:ℝ)/1000+136/1000)/(4*(7195/10000)) +
        (7196/10000)*(1217/1000) - (2*(7195/10000)+1)/2*(2718/1000) +
        (1-7195/10000)/2*(368/1000) := by
      gcongr <;> first | assumption | linarith [hp.1, hp.2.1]
    _ ≤ -gamma a := by linarith [hp.2.2.2.1]

lemma convex_chord {f : ℝ → ℝ} {D : Set ℝ} {u v z : ℝ}
    (hf : ConvexOn ℝ D f) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u < v) (huz : u ≤ z) (hzv : z ≤ v) :
    f z ≤ (v-z)/(v-u)*f u + (z-u)/(v-u)*f v := by
  have hd : 0 < v-u := sub_pos.mpr huv
  have ha : 0 ≤ (v-z)/(v-u) := div_nonneg (sub_nonneg.mpr hzv) hd.le
  have hb : 0 ≤ (z-u)/(v-u) := div_nonneg (sub_nonneg.mpr huz) hd.le
  have hab : (v-z)/(v-u)+(z-u)/(v-u)=1 := by field_simp <;> ring
  have he : (v-z)/(v-u)*u+(z-u)/(v-u)*v=z := by field_simp <;> ring
  have hh := hf.2 hu hv ha hb hab
  simpa only [smul_eq_mul, he] using hh



theorem radialH_bound {a z : ℝ} (ha : IsAlpha a) (hz : 0 ≤ z) (hzu : z ≤ 2) :
    radialH a z ≤ -gamma a * tau (Real.log a) z := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb : 0 < beta a := by linarith [hp.1]
  have hbu : beta a ≤ 72/100 := by linarith [hp.2.1]
  have hr0 : 0 ≤ rho a := by linarith [hr.1]
  have hru : rho a ≤ 1/10 := by linarith [hr.2]
  have hL : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  have hg : 0 ≤ gamma a := by linarith [hp.2.2.1]
  have hlo := hLo_convex hb hbu hr0 hru (show Real.log a ≤ 543/1000 by linarith [hp.2.2.2.2.2])
  have hhi := hHi_convex hb hbu hr0 hru hp.2.2.2.2.1.le
  unfold radialH
  split_ifs with hzL
  · have hh := convex_chord hlo (show 0 ∈ Set.Icc 0 (Real.log a) by exact ⟨le_rfl,hL.le⟩)
      (show Real.log a ∈ Set.Icc 0 (Real.log a) by exact ⟨hL.le,le_rfl⟩) hL hz hzL
    rw [hLo_at_zero, hLo_at_log ha] at hh
    rw [tau_first hL hz hzL]
    convert hh using 1 <;> field_simp [ne_of_gt hL] <;> ring
  · have hzL' : Real.log a ≤ z := le_of_lt (lt_of_not_ge hzL)
    by_cases hz2L : z ≤ 2*Real.log a
    · have hh := convex_chord hhi (show Real.log a ∈ Set.Ici (Real.log a) by simp)
        (show 2*Real.log a ∈ Set.Ici (Real.log a) by simp only [Set.mem_Ici]; linarith)
        (show Real.log a < 2*Real.log a by linarith) hzL' hz2L
      rw [hHi_at_log ha] at hh
      have hcoef : 0 ≤ (z-Real.log a)/(2*Real.log a-Real.log a) := div_nonneg (by linarith) (by linarith)
      have hbnd := mul_le_mul_of_nonneg_left (hHi_at_two_log ha) hcoef
      rw [tau_second hL hzL' hz2L]
      have heq : (2*Real.log a-z)/(2*Real.log a-Real.log a)*gamma a +
          (z-Real.log a)/(2*Real.log a-Real.log a)*(-gamma a) =
          -gamma a*(-3+2*z/Real.log a) := by
        rw [show 2*Real.log a-Real.log a=Real.log a by ring]
        field_simp [ne_of_gt hL] <;> ring
      linarith
    · have hz2L' : 2*Real.log a ≤ z := le_of_lt (lt_of_not_ge hz2L)
      have hh := convex_chord hhi
        (show 2*Real.log a ∈ Set.Ici (Real.log a) by simp only [Set.mem_Ici]; linarith)
        (show (2:ℝ) ∈ Set.Ici (Real.log a) by simp only [Set.mem_Ici]; linarith [hp.2.2.2.2.2])
        (show 2*Real.log a < 2 by linarith [hp.2.2.2.2.2]) hz2L' hzu
      have hd : 0 < 2-2*Real.log a := by linarith [hp.2.2.2.2.2]
      have hc1 : 0 ≤ (2-z)/(2-2*Real.log a) := div_nonneg (by linarith) hd.le
      have hc2 : 0 ≤ (z-2*Real.log a)/(2-2*Real.log a) := div_nonneg (by linarith) hd.le
      have hb1 := mul_le_mul_of_nonneg_left (hHi_at_two_log ha) hc1
      have hb2 := mul_le_mul_of_nonneg_left (hHi_at_two ha) hc2
      have heq : (2-z)/(2-2*Real.log a)*(-gamma a) +
          (z-2*Real.log a)/(2-2*Real.log a)*(-gamma a) = -gamma a := by
        rw [← add_mul, ← add_div]
        rw [show (2-z)+(z-2*Real.log a) = 2-2*Real.log a by ring]
        rw [div_self (ne_of_gt hd), one_mul]
      have ht := mul_le_mul_of_nonneg_left (tau_le_one (z := z) hL) hg
      linarith


lemma correction_formula (b p z : ℝ) :
    correction b p z = -3*b/4*Real.exp (p*z)+b/2*Real.exp (z/2) := by
  simp [correction, expSum, Fin.sum_univ_succ]
  ring_nf
  simp
lemma correction_convex {b p : ℝ} (hb : 0 ≤ b) (hp : 0 ≤ p) (hpu : p ≤ 1/10) :
    ConvexOn ℝ (Set.Ici 0) (correction b p) := by
  apply expSum_convex _ _ (convex_Ici _)
  intro z hz
  change 0 ≤ z at hz
  have he : Real.exp (p*z) ≤ Real.exp (z/2) := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : p^2 ≤ (1:ℝ)/100 := by nlinarith
  have hc : 0 ≤ b/8-3*b*p^2/4 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hsq)]
  have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ b/8 by positivity)
  have h2 := mul_nonneg hc (Real.exp_nonneg (p*z))
  simp [expSum, Fin.sum_univ_succ]
  ring_nf at h1 h2 ⊢
  linarith

lemma convex_const_bound {f : ℝ → ℝ} {D : Set ℝ} {u v z k : ℝ}
    (hf : ConvexOn ℝ D f) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u < v) (huz : u ≤ z) (hzv : z ≤ v) (hfu : f u ≤ k) (hfv : f v ≤ k) : f z ≤ k := by
  have hd : 0 < v-u := sub_pos.mpr huv
  have hh := convex_chord hf hu hv huv huz hzv
  have h1 := mul_le_mul_of_nonneg_left hfu (div_nonneg (sub_nonneg.mpr hzv) hd.le)
  have h2 := mul_le_mul_of_nonneg_left hfv (div_nonneg (sub_nonneg.mpr huz) hd.le)
  have he : (v-z)/(v-u)*k+(z-u)/(v-u)*k=k := by field_simp <;> ring
  linarith

theorem middle_at_log {a : ℝ} (ha : IsAlpha a) :
    gamma a + correction (beta a) (rho a) (Real.log a) ≤ -gamma a := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb : 0 < beta a := by linarith [hp.1]
  have hL : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  have hU : 1 ≤ Real.exp (rho a*Real.log a) := Real.one_le_exp (mul_nonneg (by linarith [hr.1]) hL.le)
  have hQ : Real.exp (Real.log a/2) ≤ (1312:ℝ)/1000 := by
    have hh := exp_half_sq (Real.log a)
    rw [Real.exp_log (show 0 < a by linarith [ha.1])] at hh
    nlinarith [ha.2.1, Real.exp_pos (Real.log a/2)]
  rw [correction_formula]
  have hneg : 3*beta a/4*Real.exp (rho a*Real.log a) ≥ 3*((7195:ℝ)/10000)/4*1 := by
    gcongr <;> linarith [hp.1]
  have hpos : beta a/2*Real.exp (Real.log a/2) ≤ ((7196:ℝ)/10000)/2*(1312/1000) := by
    gcongr <;> linarith [hp.2.1]
  linarith [hp.2.2.2.1]

theorem middle_at_three_halves {a : ℝ} (ha : IsAlpha a) :
    hHi (beta a) (rho a) (3/2) + correction (beta a) (rho a) (3/2) ≤ -gamma a := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb : 0 < beta a := by linarith [hp.1]
  have hA : Real.exp ((1-rho a)*(3/2)) ≤ (3875:ℝ)/1000 := by
    have he : Real.exp ((1-rho a)*(3/2)) ≤ Real.exp (2*((2709:ℝ)/4000)) :=
      Real.exp_le_exp.mpr (by linarith [hr.1])
    rw [exp_double] at he
    nlinarith [exp_bound_11.1, exp_bound_11.2]
  have hB : Real.exp (-(1+rho a)*(3/2)) ≤ (193:ℝ)/1000 := by
    have he : Real.exp (-(1+rho a)*(3/2)) ≤ Real.exp (2*(-(3291:ℝ)/4000)) :=
      Real.exp_le_exp.mpr (by linarith [hr.1])
    rw [exp_double] at he
    nlinarith [exp_bound_12.1, exp_bound_12.2]
  have hC : Real.exp (rho a*(3/2)) ≤ (1159:ℝ)/1000 := by
    have he := Real.exp_le_exp.mpr (show rho a*(3/2) ≤ (147:ℝ)/1000 by linarith [hr.2])
    linarith [exp_bound_13.2]
  have hD : (2117:ℝ)/1000 ≤ Real.exp ((3/2)/2) := by norm_num; linarith [exp_bound_14.1]
  have hE : Real.exp (-(3/2)/2) ≤ (473:ℝ)/1000 := by norm_num; linarith [exp_bound_15.2]
  rw [hHi_formula, correction_formula]
  have hid :
    (Real.exp ((1-rho a)*(3/2))+Real.exp (-(1+rho a)*(3/2)))/(4*beta a)+
      beta a*Real.exp (rho a*(3/2))-(2*beta a+1)/2*Real.exp ((3/2)/2)+
      (1-beta a)/2*Real.exp (-(3/2)/2)+
      (-3*beta a/4*Real.exp (rho a*(3/2))+beta a/2*Real.exp ((3/2)/2)) =
    (Real.exp ((1-rho a)*(3/2))+Real.exp (-(1+rho a)*(3/2)))/(4*beta a)+
      beta a/4*Real.exp (rho a*(3/2))-(beta a+1)/2*Real.exp ((3/2)/2)+
      (1-beta a)/2*Real.exp (-(3/2)/2) := by ring
  rw [hid]
  calc
    _ ≤ ((3875:ℝ)/1000+193/1000)/(4*(7195/10000)) +
        (7196/10000)/4*(1159/1000) - (7195/10000+1)/2*(2117/1000) +
        (1-7195/10000)/2*(473/1000) := by
      gcongr <;> first | assumption | linarith [hp.1, hp.2.1]
    _ ≤ -gamma a := by linarith [hp.2.2.2.1]

theorem radialM_bound {a z : ℝ} (ha : IsAlpha a) (hz : 0 ≤ z) (hzu : z ≤ 3/2) :
    radialH a z + correction (beta a) (rho a) z ≤ -gamma a := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb : 0 < beta a := by linarith [hp.1]
  have hbu : beta a ≤ 72/100 := by linarith [hp.2.1]
  have hr0 : 0 ≤ rho a := by linarith [hr.1]
  have hru : rho a ≤ 1/10 := by linarith [hr.2]
  have hL : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  have hlo := hLo_convex hb hbu hr0 hru (show Real.log a ≤ 543/1000 by linarith [hp.2.2.2.2.2])
  have hhi := hHi_convex hb hbu hr0 hru hp.2.2.2.2.1.le
  have hcor := correction_convex hb.le hr0 hru
  unfold radialH
  split_ifs with hzL
  · have hc := hcor.subset (show Set.Icc 0 (Real.log a) ⊆ Set.Ici 0 from fun _ hx => hx.1) (convex_Icc _ _)
    apply convex_const_bound (hlo.add hc)
      (show 0 ∈ Set.Icc 0 (Real.log a) from ⟨le_rfl,hL.le⟩)
      (show Real.log a ∈ Set.Icc 0 (Real.log a) from ⟨hL.le,le_rfl⟩) hL hz hzL
    · simp only [Pi.add_apply, hLo_at_zero, correction_formula, mul_zero, zero_div, Real.exp_zero]
      linarith
    · simpa only [Pi.add_apply, hLo_at_log ha] using middle_at_log ha
  · have hc := hcor.subset (show Set.Ici (Real.log a) ⊆ Set.Ici 0 from fun _ hx => hL.le.trans hx) (convex_Ici _)
    apply convex_const_bound (hhi.add hc)
      (show Real.log a ∈ Set.Ici (Real.log a) by simp)
      (show (3/2:ℝ) ∈ Set.Ici (Real.log a) by simp only [Set.mem_Ici]; linarith [hp.2.2.2.2.2])
      (show Real.log a < 3/2 by linarith [hp.2.2.2.2.2]) (le_of_lt (lt_of_not_ge hzL)) hzu
    · simpa only [Pi.add_apply, hHi_at_log ha] using middle_at_log ha
    · exact middle_at_three_halves ha

-- Algebraic coordinates q = exp(z/2), u = exp(rho*z).



/-! ===================== CASE 1: large c, c >= beta * exp(z); used for 0 <= z <= 2 ===================== -/

lemma potential_large {b q u c : ℝ} (hb : 0 < b) (hq : 1 ≤ q)
    (hu : 0 < u) (hc : b*q^2 ≤ c) :
    potential b q u c ≤ envelope b q u := by
  have hq0 : 0 < q := by linarith
  have hbc : b ≤ c := by nlinarith [mul_nonneg hb.le (show 0 ≤ q^2-1 by nlinarith)]
  have h1 : pos (c-b*q^2) = c-b*q^2 := max_eq_left (by linarith)
  have h2 : pos (c-b) = c-b := max_eq_left (by linarith)
  have hid : potential b q u c = envelope b q u -
      (c-2*b*u*q)^2/(4*b*u*q^2) := by
    unfold potential envelope
    rw [h1,h2]
    field_simp
    <;> ring
  rw [hid]
  have : 0 ≤ (c-2*b*u*q)^2/(4*b*u*q^2) := by positivity
  linarith

/-! ===================== CASE 2: small c, c <= beta ===================== -/

lemma potential_small {b q u c : ℝ} (hb : 0 < b) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (hc : q^2-1 ≤ c) (hcu : c ≤ b) :
    potential b q u c ≤ -b+1/(2*b) := by
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < u := by linarith
  have hc0 : 0 ≤ c := by nlinarith
  have hcb : c ≤ b*q^2 := by nlinarith [mul_nonneg hb.le (show 0 ≤ q^2-1 by nlinarith)]
  have h1 : pos (c-b*q^2) = 0 := max_eq_right (by linarith)
  have h2 : pos (c-b) = 0 := max_eq_right (by linarith)
  have hpos : b+1-q^2 ≤ pos (b+1-q^2) := le_max_left _ _
  have hn : (0+0-(b+1)*q^2+1-pos (b+1-q^2))/(2*q) ≤ -b := by
    apply (div_le_iff₀ (by positivity : 0 < 2*q)).2
    nlinarith [mul_nonneg hb.le (sq_nonneg (q-1))]
  have hs : q^4+1-c^2 ≤ 2*q^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ c+(q^2-1) by nlinarith)]
  have hd : (q^4+1-c^2)/(4*b*u*q^2) ≤ 1/(2*b) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*b*u*q^2)).2
    have hid : 1/(2*b)*(4*b*u*q^2) = 2*u*q^2 := by field_simp; ring
    rw [hid]
    nlinarith [mul_nonneg (show 0 ≤ u-1 by linarith) (sq_nonneg q)]
  unfold potential
  rw [h1,h2]
  linarith

/-! ===================== CASE 3: intermediate c, beta <= c <= beta * exp(z) ===================== -/

lemma potential_middle {b q u c : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hu : 0 < u) (hc : b ≤ c) (hcu : c ≤ b*q^2) :
    potential b q u c ≤ envelope b q u -3*b*u/4+b*q/2 := by
  have h1 : pos (c-b*q^2) = 0 := max_eq_right (by linarith)
  have h2 : pos (c-b) = c-b := max_eq_left (by linarith)
  have hid : potential b q u c = envelope b q u -3*b*u/4+b*q/2 -
      (c-b*u*q)^2/(4*b*u*q^2) := by
    unfold potential envelope
    rw [h1,h2]
    field_simp
    <;> ring
  rw [hid]
  have : 0 ≤ (c-b*u*q)^2/(4*b*u*q^2) := by positivity
  linarith

lemma envelope_eq_radialH {a z : ℝ} (ha : IsAlpha a) :
    envelope (beta a) (Real.exp (z/2)) (Real.exp (rho a*z)) = radialH a z := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hb : 0 < beta a := by dsimp [beta]; linarith [ha.1]
  have hq := exp_half_sq z
  have he : Real.exp z = Real.exp (z/2)^2 := hq.symm
  have hq0 := Real.exp_pos (z/2)
  have hu0 := Real.exp_pos (rho a*z)
  unfold radialH
  split_ifs with hz
  · have hx : Real.exp z ≤ a := by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hz
    have hpos : pos (beta a+1-Real.exp (z/2)^2) = beta a+1-Real.exp (z/2)^2 :=
      max_eq_left (by dsimp [beta]; linarith)
    rw [envelope,hpos,hLo_algebraic,he]
    field_simp
    dsimp [beta]
    <;> ring
  · have hx : a ≤ Real.exp z := by
      have hh := Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hz))
      simpa [Real.exp_log ha0] using hh
    have hpos : pos (beta a+1-Real.exp (z/2)^2) = 0 :=
      max_eq_right (by dsimp [beta]; linarith)
    rw [envelope,hpos,hHi_algebraic,he]
    field_simp
    dsimp [beta]
    <;> ring

lemma middle_feasible {a z c : ℝ} (ha : IsAlpha a)
    (hc : Real.exp z-1 ≤ c) (hcu : c ≤ beta a*Real.exp z) : z ≤ 3/2 := by
  have hp := basic_parameter_bounds ha
  by_contra hz
  have he : Real.exp (2*((3:ℝ)/4)) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith)
  rw [exp_double] at he
  have hex : (448:ℝ)/100 ≤ Real.exp z := by nlinarith [exp_bound_14.1, exp_bound_14.2]
  have hprod := mul_nonneg (show 0 ≤ (7196:ℝ)/10000-beta a by linarith [hp.2.1]) (Real.exp_nonneg z)
  linarith

/-! ===================== CASE 4: large log ratio, z >= 2 ===================== -/

lemma potential_tail {b q u c : ℝ} (hb : (7195:ℝ)/10000 ≤ b)
    (hbu : b ≤ 7196/10000) (hq : 1 ≤ q) (hu : 1 ≤ u)
    (hc : q^2-1 ≤ c) (haq : b+1 ≤ q^2)
    (hactive : b*q^2 ≤ q^2-1) (hvertex : 2*b*u*q ≤ q^2-1) :
    potential b q u c ≤ -b+1/(2*b) := by
  have hb0 : 0 < b := by linarith
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < u := by linarith
  have hbc : b ≤ c := by nlinarith [mul_nonneg hb0.le (show 0 ≤ q^2-1 by nlinarith)]
  have h1 : pos (c-b*q^2) = c-b*q^2 := max_eq_left (by linarith)
  have h2 : pos (c-b) = c-b := max_eq_left (by linarith)
  have h3 : pos (b+1-q^2) = 0 := max_eq_right (by linarith)
  have hid : potential b q u c =
      -((2*b-1)*q^2+(b+1))/(2*q)+1/(2*b*u) -
      ((c-2*b*u*q)^2-(q^2-1-2*b*u*q)^2)/(4*b*u*q^2) := by
    unfold potential
    rw [h1,h2,h3]
    field_simp
    <;> ring
  have hs : 0 ≤ (c-2*b*u*q)^2-(q^2-1-2*b*u*q)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ c-(q^2-1) by linarith)
      (show 0 ≤ (c-2*b*u*q)+(q^2-1-2*b*u*q) by linarith)]
  have hd : 0 ≤ ((c-2*b*u*q)^2-(q^2-1-2*b*u*q)^2)/(4*b*u*q^2) := div_nonneg hs (by positivity)
  have huinv : 1/(2*b*u) ≤ 1/(2*b) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hdis : 0 ≤ (2*b-1)*(b+1)-b^2 := by nlinarith
  have hpoly : 0 ≤ (2*b-1)*q^2-2*b*q+(b+1) := by
    have hsq := sq_nonneg ((2*b-1)*q-b)
    have hid2 : (2*b-1)*((2*b-1)*q^2-2*b*q+(b+1)) =
        ((2*b-1)*q-b)^2+((2*b-1)*(b+1)-b^2) := by ring
    have hf : 0 < 2*b-1 := by linarith
    nlinarith only [hid2, hsq, hdis, hf]
  have hfrac : b ≤ ((2*b-1)*q^2+(b+1))/(2*q) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*q)).2
    linarith
  rw [hid, neg_div]
  linarith only [hd, huinv, hfrac]

lemma tail_parameters {a z : ℝ} (ha : IsAlpha a) (hz : 2 ≤ z) :
    beta a+1 ≤ (Real.exp (z/2))^2 ∧
    beta a*(Real.exp (z/2))^2 ≤ (Real.exp (z/2))^2-1 ∧
    2*beta a*Real.exp (rho a*z)*Real.exp (z/2) ≤ (Real.exp (z/2))^2-1 := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hx : (7:ℝ) ≤ Real.exp z := by
    have he := Real.exp_le_exp.mpr hz
    have he2 : Real.exp (2:ℝ) = (Real.exp 1)^2 := by simpa using exp_double 1
    rw [he2] at he
    nlinarith [exp_bound_9.1, exp_bound_9.2]
  rw [exp_half_sq]
  have hprod := mul_nonneg (show 0 ≤ (7196:ℝ)/10000-beta a by linarith [hp.2.1]) (Real.exp_nonneg z)
  constructor
  · linarith [hp.2.1]
  constructor
  · linarith
  have hexp : (18:ℝ)/10 ≤ Real.exp ((1/2-rho a)*z) := by
    have ht := Real.add_one_le_exp ((1/2-rho a)*z)
    have hm := mul_nonneg (show 0 ≤ (1/2-rho a)-4/10 by linarith [hr.2]) (show 0 ≤ z by linarith)
    linarith
  have hid : Real.exp ((1/2-rho a)*z)*Real.exp (rho a*z)*Real.exp (z/2) = Real.exp z := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hexp
    (mul_nonneg (Real.exp_nonneg (rho a*z)) (Real.exp_nonneg (z/2)))
  have hbnd := mul_nonneg (show 0 ≤ (144:ℝ)/100-2*beta a by linarith [hp.2.1])
    (mul_nonneg (Real.exp_nonneg (rho a*z)) (Real.exp_nonneg (z/2)))
  simp only [← mul_assoc] at hm
  rw [hid] at hm
  nlinarith only [hm, hbnd, hx]

/-! ===================== EXHAUSTIVE CASE DISPATCH ===================== -/

theorem potential_bound {a z c : ℝ} (ha : IsAlpha a) (hz : 0 ≤ z)
    (hc : Real.exp z-1 ≤ c) :
    potential (beta a) (Real.exp (z/2)) (Real.exp (rho a*z)) c ≤
      -gamma a*tau (Real.log a) z := by
  have hp := basic_parameter_bounds ha
  have hr := rho_bounds ha
  have hb : 0 < beta a := by linarith [hp.1]
  have hq : 1 ≤ Real.exp (z/2) := Real.one_le_exp (by linarith)
  have hq0 := Real.exp_pos (z/2)
  have hu : 1 ≤ Real.exp (rho a*z) := Real.one_le_exp (mul_nonneg (by linarith [hr.1]) hz)
  have hu0 := Real.exp_pos (rho a*z)
  have hc' : (Real.exp (z/2))^2-1 ≤ c := by rwa [exp_half_sq]
  have hg : 0 ≤ gamma a := by linarith [hp.2.2.1]
  have hL : 0 < Real.log a := by linarith [hp.2.2.2.2.1]
  have ht : -gamma a ≤ -gamma a*tau (Real.log a) z := by
    nlinarith [tau_le_one (z:=z) hL]
  by_cases hzt : z ≤ 2
  · -- SHORT RADIAL RANGE: z <= 2
    by_cases hcL : beta a*(Real.exp (z/2))^2 ≤ c
    · -- CASE 1: both positive parts active.
      have hh := potential_large hb hq hu0 hcL
      rw [envelope_eq_radialH ha] at hh
      exact hh.trans (radialH_bound ha hz hzt)
    · by_cases hcm : beta a ≤ c
      · -- CASE 3: only (c-beta) is active.
        have hh := potential_middle hb hq0 hu0 hcm (le_of_lt (lt_of_not_ge hcL))
        rw [envelope_eq_radialH ha] at hh
        have hcz : c ≤ beta a*Real.exp z := by rw [← exp_half_sq]; exact le_of_lt (lt_of_not_ge hcL)
        have hm := radialM_bound ha hz (middle_feasible ha hc hcz)
        rw [correction_formula] at hm
        have hh' : potential (beta a) (Real.exp (z/2)) (Real.exp (rho a*z)) c ≤ -gamma a := by linarith
        exact hh'.trans ht
      · -- CASE 2: neither positive part is active.
        have hh := potential_small hb hq hu hc' (le_of_lt (lt_of_not_ge hcm))
        have he : -(beta a)+1/(2*beta a) = -gamma a := by dsimp [gamma]; ring
        rw [he] at hh
        exact hh.trans ht
  · -- CASE 4: z > 2; evaluate at the smallest feasible c.
    have hpars := tail_parameters ha (le_of_lt (lt_of_not_ge hzt))
    have hh := potential_tail hp.1.le hp.2.1.le hq hu hc' hpars.1 hpars.2.1 hpars.2.2
    have he : -(beta a)+1/(2*beta a) = -gamma a := by dsimp [gamma]; ring
    rw [he] at hh
    exact hh.trans ht

lemma potential_kernel {a z c : ℝ} (ha : IsAlpha a) (hz : 0 ≤ z) :
    potential (beta a) (Real.exp (z/2)) (Real.exp (rho a*z)) c =
    K a (Real.exp z) 1 c / Real.exp (z/2) +
      ((Real.exp z)^2+1-c^2)/(4*beta a*Real.exp (rho a*z)*Real.exp z) := by
  have he : 1 ≤ Real.exp z := Real.one_le_exp hz
  have ha1 : 1 < a := by linarith [ha.1]
  have hprod : 0 ≤ a*Real.exp z-1 := by nlinarith
  have hp : pos (a*Real.exp z-1) = a*Real.exp z-1 := max_eq_left hprod
  have h1 : Real.exp z+c-a*Real.exp z = c-beta a*Real.exp z := by dsimp [beta]; ring
  have h2 : 1+c-a*1 = c-beta a := by dsimp [beta]; ring
  unfold potential K
  rw [show (Real.exp (z/2))^4 = (Real.exp z)^2 by rw [show (Real.exp (z/2))^4 = ((Real.exp (z/2))^2)^2 by ring,exp_half_sq]]
  rw [exp_half_sq,h1,h2,hp]
  simp only [mul_one]
  have hb : beta a+1=a := by dsimp [beta]; ring
  rw [hb]
  ring

theorem kernel_exponential {a z c : ℝ} (ha : IsAlpha a) (hz : 0 ≤ z)
    (hc : Real.exp z-1 ≤ c) :
    K a (Real.exp z) 1 c ≤ boundRHS a (Real.exp z) 1 c := by
  have hh := potential_bound ha hz hc
  rw [potential_kernel ha hz] at hh
  have hb : 0 < beta a := by dsimp [beta]; linarith [ha.1]
  have hq := Real.exp_pos (z/2)
  have hu := Real.exp_pos (rho a*z)
  have hs : Real.sqrt (Real.exp z) = Real.exp (z/2) := by
    have hsq := Real.sq_sqrt (Real.exp_nonneg z)
    have he := exp_half_sq z
    nlinarith [Real.sqrt_nonneg (Real.exp z)]
  have heq : boundRHS a (Real.exp z) 1 c / Real.exp (z/2) =
      -gamma a*tau (Real.log a) z -
      ((Real.exp z)^2+1-c^2)/(4*beta a*Real.exp (rho a*z)*Real.exp z) := by
    unfold boundRHS
    simp only [div_one, mul_one, Real.log_exp, abs_of_nonneg hz, one_pow, hs]
    rw [show -(rho a)*z = -(rho a*z) by ring,Real.exp_neg,← exp_half_sq z]
    field_simp
    <;> ring
  apply (div_le_div_iff_of_pos_right hq).mp
  rw [heq]
  linarith

lemma pos_scale {k : ℝ} (hk : 0 ≤ k) (x : ℝ) : pos (k*x) = k*pos x := by
  unfold pos
  rw [mul_max_of_nonneg _ _ hk, mul_zero]

lemma K_scale {k : ℝ} (hk : 0 ≤ k) (a r s c : ℝ) :
    K a (k*r) (k*s) (k*c) = k*K a r s c := by
  unfold K
  rw [show k*r+k*c-a*(k*r)=k*(r+c-a*r) by ring,
      show k*s+k*c-a*(k*s)=k*(s+c-a*s) by ring,
      show a*(k*r)-k*s=k*(a*r-s) by ring,
      show a*(k*s)-k*r=k*(a*s-r) by ring]
  simp only [pos_scale hk]
  ring

lemma K_symm (a r s c : ℝ) : K a r s c = K a s r c := by unfold K; ring

lemma boundRHS_scale {k r s : ℝ} (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (a c : ℝ) :
    boundRHS a (k*r) (k*s) (k*c) = k*boundRHS a r s c := by
  have hsqrt : Real.sqrt (k*r*(k*s)) = k*Real.sqrt (r*s) := by
    rw [show k*r*(k*s)=k^2*(r*s) by ring,Real.sqrt_mul (sq_nonneg k),Real.sqrt_sq hk.le]
  have hdiv : k*r/(k*s)=r/s := by field_simp <;> ring
  unfold boundRHS
  rw [hsqrt,hdiv]
  by_cases hb : beta a = 0
  · simp only [hb, mul_zero, zero_mul, div_zero, neg_zero, zero_sub]
    ring
  · have hsr : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    have hss : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
    field_simp [ne_of_gt hk, hb, hsr, hss]
    <;> ring

lemma boundRHS_symm {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (a c : ℝ) :
    boundRHS a r s c = boundRHS a s r c := by
  have hlog : Real.log (s/r) = -Real.log (r/s) := by
    rw [Real.log_div (ne_of_gt hs) (ne_of_gt hr),Real.log_div (ne_of_gt hr) (ne_of_gt hs)]
    ring
  unfold boundRHS
  rw [hlog,abs_neg,tau_even,show s*r=r*s by ring]
  ring

-- Scaling and swapping extend the normalized result to arbitrary radii.
/-! ===================== UNDO NORMALIZATION: SCALING AND SYMMETRY ===================== -/

theorem kernel_ordered {a r s c : ℝ} (ha : IsAlpha a) (hr : 0 < r)
    (hs : 0 < s) (hrs : s ≤ r) (hc : r-s ≤ c) :
    K a r s c ≤ boundRHS a r s c := by
  have hratio : 0 < r/s := div_pos hr hs
  have hratio1 : 1 ≤ r/s := (le_div_iff₀ hs).2 (by simpa using hrs)
  have hz : 0 ≤ Real.log (r/s) := Real.log_nonneg hratio1
  have he := Real.exp_log hratio
  have hc' : Real.exp (Real.log (r/s))-1 ≤ c/s := by
    rw [he]
    apply (le_div_iff₀ hs).2
    have hid : (r/s-1)*s=r-s := by field_simp
    rwa [hid]
  have hh := kernel_exponential ha hz hc'
  have hm := mul_le_mul_of_nonneg_left hh hs.le
  rw [← K_scale hs.le,← boundRHS_scale hs (Real.exp_pos _) (by norm_num : (0:ℝ)<1)] at hm
  simpa only [he, mul_div_cancel₀ _ (ne_of_gt hs),mul_one] using hm

theorem kernel_bound {a r s c : ℝ} (ha : IsAlpha a) (hr : 0 < r)
    (hs : 0 < s) (hc : |r-s| ≤ c) :
    K a r s c ≤ boundRHS a r s c := by
  by_cases hrs : s ≤ r
  · exact kernel_ordered ha hr hs hrs ((le_abs_self _).trans hc)
  · rw [K_symm a r s c,boundRHS_symm hr hs]
    apply kernel_ordered ha hs hr (le_of_lt (lt_of_not_ge hrs))
    have hh := neg_le_abs (r-s)
    linarith

/-- Lemma 1.2 of euclidean-lmp.tex, with its original parameter and certificate. -/
theorem lemma12 : Lemma12 := by
  refine ⟨alpha_exists_unique, ?_⟩
  intro a ha r s c hr hs hc _
  exact kernel_bound ha hr hs hc

/-- Requested median certificate, including existence and uniqueness of alpha. -/
theorem median_certificate : Lemma12 := lemma12

#print axioms median_certificate

end
end Clustering
