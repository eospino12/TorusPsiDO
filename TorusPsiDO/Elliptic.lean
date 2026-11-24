import TorusPsiDO.Quantization
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NoncommRing

/-!
# Elliptic operators on `𝕋ⁿ` (Thesis, Chapter 3)

* Definition 3.0.1 and the computation after it: a left and a right parametrix agree modulo
  the smoothing operators: `S = P + R₂P - SR₁`.
* Remark 2.0.20: the Sobolev spaces `H^s(𝕋ⁿ)`, in terms of Fourier coefficients, and the
  inclusions `H^s ⊆ H^t` for `t ≤ s`.
* Definition 3.0.2: elliptic and strongly elliptic symbols of order `m`.
* Example 3.0.3: `-Δ` is (strongly) elliptic of order 2.
* Theorem 3.0.4 (ellipticity part): `(-Δ)^{ν/2} + Q(x)` is strongly elliptic of order `ν`
  for `ν > 0` and `Q` continuous on `𝕋ⁿ`.
* Equation (3.9), elliptic regularity, for Fourier multipliers: if `P = p(D)` is elliptic of
  order `m`, `Pu = f` and `f ∈ H^s`, then `u ∈ H^{s+m}`.

The Fredholm property in Theorem 3.0.4 is proved in `Fredholm.lean`.  Not formalized: the
construction (3.2)–(3.6) of the parametrix for symbols depending on `x`, which relies on the
symbolic calculus (composition and asymptotic sums in `Ψ^m_{ρ,δ}`), not available in Mathlib.
-/

open Complex Finset Real Filter

namespace TorusPsiDO

variable {n : ℕ}

/-! ### Definition 3.0.1: parametrices -/

/-- **After Definition 3.0.1.** If `LP - I = R₁` and `SL - I = R₂`, then
`S = P + R₂ P - S R₁`. -/
theorem left_eq_right_parametrix {R : Type*} [Ring R] (L P S R₁ R₂ : R)
    (h₁ : L * P - 1 = R₁) (h₂ : S * L - 1 = R₂) : S = P + R₂ * P - S * R₁ := by
  rw [← h₁, ← h₂]
  noncomm_ring

/-- Consequently, if `R₁, R₂` belong to a two-sided ideal `I` (for example, the smoothing
operators `Ψ^{-∞}`), then `S - P ∈ I`: a left and a right parametrix coincide modulo `I`. -/
theorem parametrix_sub_mem {R : Type*} [Ring R] (I : AddSubgroup R)
    (hl : ∀ a b, b ∈ I → a * b ∈ I) (hr : ∀ a b, a ∈ I → a * b ∈ I) (L P S : R)
    (h₁ : L * P - 1 ∈ I) (h₂ : S * L - 1 ∈ I) : S - P ∈ I := by
  have h := left_eq_right_parametrix L P S _ _ rfl rfl
  have : S - P = (S * L - 1) * P - S * (L * P - 1) := by
    conv_lhs => rw [h]
    abel
  rw [this]
  exact I.sub_mem (hr _ _ h₂) (hl _ _ h₁)

/-! ### Remark 2.0.20: Sobolev spaces -/

/-- `u ∈ H^s(𝕋ⁿ)`, in terms of its Fourier coefficients `û`:
`‖u‖²_{H^s} = ∑_ξ ⟨ξ⟩^{2s} |û(ξ)|² < ∞`. -/
def InSobolev (s : ℝ) (u : (Fin n → ℤ) → ℂ) : Prop :=
  Summable fun ξ => jbr ξ ^ (2 * s) * ‖u ξ‖ ^ 2

/-- `H^s(𝕋ⁿ) ⊆ H^t(𝕋ⁿ)` for `t ≤ s`. -/
theorem InSobolev.mono {s t : ℝ} (hts : t ≤ s) {u : (Fin n → ℤ) → ℂ} (hu : InSobolev s u) :
    InSobolev t u := by
  refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_) hu
  · exact mul_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (jbr_rpow_le_rpow ξ (by linarith)) (sq_nonneg _)

/-! ### Definition 3.0.2: ellipticity -/

/-- **Definition 3.0.2.** `σ` is elliptic of order `m`:
`|σ(x, ξ)| ≥ C₀ ⟨ξ⟩^m` for `|ξ| ≥ n₀`. -/
def IsElliptic (m : ℝ) (σ : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) : Prop :=
  ∃ n₀ C₀ : ℝ, 0 < n₀ ∧ 0 < C₀ ∧ ∀ x ξ, n₀ ≤ normZ ξ → C₀ * jbr ξ ^ m ≤ ‖σ x ξ‖

/-- **Definition 3.0.2.** `σ` is strongly elliptic of order `m`:
`Re σ(x, ξ) ≥ C₀ ⟨ξ⟩^m` for `|ξ| ≥ n₀`. -/
def IsStronglyElliptic (m : ℝ) (σ : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) : Prop :=
  ∃ n₀ C₀ : ℝ, 0 < n₀ ∧ 0 < C₀ ∧ ∀ x ξ, n₀ ≤ normZ ξ → C₀ * jbr ξ ^ m ≤ (σ x ξ).re

/-- Strong ellipticity implies ellipticity. -/
theorem IsStronglyElliptic.isElliptic {m : ℝ} {σ : (Fin n → ℝ) → (Fin n → ℤ) → ℂ}
    (h : IsStronglyElliptic m σ) : IsElliptic m σ := by
  obtain ⟨n₀, C₀, hn₀, hC₀, hσ⟩ := h
  exact ⟨n₀, C₀, hn₀, hC₀, fun x ξ hξ => (hσ x ξ hξ).trans (Complex.re_le_norm _)⟩

/-- **Example 3.0.3.** `-Δ`, with symbol `4π²|ξ|²`, is strongly elliptic of order 2. -/
theorem lap_stronglyElliptic : IsStronglyElliptic (n := n) 2 (fun _ ξ => lapSymbol ξ) := by
  refine ⟨1, 2 * π ^ 2, one_pos, by positivity, fun x ξ hξ => ?_⟩
  show 2 * π ^ 2 * jbr ξ ^ (2 : ℝ) ≤ (lapSymbol ξ).re
  rw [lapSymbol_eq, Complex.ofReal_re, Real.rpow_two, jbr_sq_eq]
  have : 1 ≤ normZ ξ ^ 2 := by nlinarith [normZ_nonneg ξ]
  nlinarith [Real.pi_pos]

/-- A continuous `1`-periodic function has real part bounded below (`𝕋ⁿ` is compact). -/
theorem exists_re_lower_bound (Q : (Fin n → ℝ) → ℂ) (hc : Continuous Q) (hp : IsPeriodic Q) :
    ∃ C₁ : ℝ, ∀ x, C₁ ≤ (Q x).re := by
  set K : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hne : K.Nonempty := ⟨0, fun i _ => by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := hK.exists_isMinOn hne (Complex.continuous_re.comp hc).continuousOn
  refine ⟨(Q x₀).re, fun x => ?_⟩
  set k : Fin n → ℤ := fun i => ⌊x i⌋
  have hy : x - toR k ∈ K := by
    intro i _
    simp only [Pi.sub_apply, toR, k, Set.mem_Icc]
    exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩
  have hx : Q x = Q (x - toR k) := by
    rw [← hp (x - toR k) k, sub_add_cancel]
  rw [hx]
  exact isMinOn_iff.mp hx₀ _ hy

/-- **Theorem 3.0.4 (ellipticity).** For `ν > 0` and `Q` continuous on `𝕋ⁿ`, the operator
`(-Δ)^{ν/2} + Q(x)`, with symbol `(2π|ξ|)^ν + Q(x)`, is strongly elliptic of order `ν`
(hence elliptic). -/
theorem fracLap_add_potential_stronglyElliptic (ν : ℝ) (hν : 0 < ν)
    (Q : (Fin n → ℝ) → ℂ) (hc : Continuous Q) (hp : IsPeriodic Q) :
    IsStronglyElliptic ν (fun x ξ => (((2 * π * normZ ξ) ^ ν : ℝ) : ℂ) + Q x) := by
  obtain ⟨C₁, hC₁⟩ := exists_re_lower_bound Q hc hp
  set A := |2 * C₁|
  refine ⟨max 1 (A ^ ν⁻¹), π ^ ν / 2, lt_of_lt_of_le one_pos (le_max_left _ _),
    by positivity, fun x ξ hξ => ?_⟩
  have h1 : 1 ≤ normZ ξ := le_trans (le_max_left _ _) hξ
  have hX0 : 0 ≤ normZ ξ := normZ_nonneg ξ
  set X := normZ ξ ^ ν with hXdef
  have hX : 0 ≤ X := Real.rpow_nonneg hX0 _
  have hab : 1 ≤ (2 : ℝ) ^ ν * π ^ ν := by
    rw [← Real.mul_rpow (by norm_num) Real.pi_pos.le]
    exact Real.one_le_rpow (by linarith [Real.two_le_pi]) hν.le
  have hsym : (2 * π * normZ ξ) ^ ν = 2 ^ ν * π ^ ν * X := (fracLap_symbol ν ξ).symm
  have hjbr : jbr ξ ^ ν ≤ 2 ^ ν * X := by
    rw [hXdef, ← Real.mul_rpow (by norm_num) hX0]
    exact Real.rpow_le_rpow (jbr_pos ξ).le (jbr_le_two_normZ h1) hν.le
  have hXA : A ≤ X := by
    have : A ^ ν⁻¹ ≤ normZ ξ := le_trans (le_max_right _ _) hξ
    calc A = (A ^ ν⁻¹) ^ ν := (Real.rpow_inv_rpow (abs_nonneg _) hν.ne').symm
      _ ≤ normZ ξ ^ ν := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) this hν.le
  have hA : -(2 * C₁) ≤ A := neg_le_abs _
  have hre : ((((2 * π * normZ ξ) ^ ν : ℝ) : ℂ) + Q x).re = (2 * π * normZ ξ) ^ ν + (Q x).re := by
    simp
  rw [hre, hsym]
  have hQ := hC₁ x
  have hpi : 0 < π ^ ν := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : 0 < (2 : ℝ) ^ ν := Real.rpow_pos_of_pos (by norm_num) _
  have hP : X ≤ 2 ^ ν * π ^ ν * X := by nlinarith
  calc π ^ ν / 2 * jbr ξ ^ ν ≤ π ^ ν / 2 * (2 ^ ν * X) :=
        mul_le_mul_of_nonneg_left hjbr (by positivity)
    _ ≤ 2 ^ ν * π ^ ν * X + (Q x).re := by nlinarith

/-! ### Equation (3.9): elliptic regularity for Fourier multipliers -/

/-- Only finitely many `ξ ∈ ℤⁿ` satisfy `|ξ| < R`. -/
theorem finite_normZ_lt (R : ℝ) : {ξ : Fin n → ℤ | normZ ξ < R}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-⌈R⌉) ⌈R⌉)
    (fun _ => Set.finite_Icc _ _)).subset fun ξ hξ i _ => ?_
  have h := (abs_coord_le_normZ ξ i).trans_lt hξ
  have hR : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
  rw [abs_lt] at h
  constructor
  · have : (-(⌈R⌉ : ℝ)) < (ξ i : ℝ) := by linarith
    exact_mod_cast this.le
  · have : (ξ i : ℝ) < (⌈R⌉ : ℝ) := by linarith
    exact_mod_cast this.le

/-- **Equation (3.9) for Fourier multipliers (elliptic regularity).** Let `P = p(D)` be elliptic
of order `m`.  If `Pu = f`, i.e. `p(ξ) û(ξ) = f̂(ξ)`, and `f ∈ H^s(𝕋ⁿ)`, then
`u ∈ H^{s+m}(𝕋ⁿ)`. -/
theorem elliptic_regularity_multiplier (m s : ℝ) (p : (Fin n → ℤ) → ℂ)
    (hp : IsElliptic m (fun _ ξ => p ξ)) (u f : (Fin n → ℤ) → ℂ)
    (hPu : ∀ ξ, p ξ * u ξ = f ξ) (hf : InSobolev s f) : InSobolev (s + m) u := by
  obtain ⟨n₀, C₀, -, hC₀, hbound⟩ := hp
  refine Summable.of_norm_bounded_eventually (g := fun ξ => (C₀⁻¹) ^ 2 *
    (jbr ξ ^ (2 * s) * ‖f ξ‖ ^ 2)) (hf.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine (finite_normZ_lt n₀).subset fun ξ hξ => ?_
  simp only [Set.mem_setOf_eq] at hξ ⊢
  by_contra hlt
  push Not at hlt
  apply hξ
  have hb := hbound 0 ξ hlt
  have hJ := jbr_pos ξ
  have hpow : jbr ξ ^ (2 * (s + m)) = jbr ξ ^ (2 * s) * (jbr ξ ^ m) ^ 2 := by
    rw [show 2 * (s + m) = 2 * s + m * 2 by ring, Real.rpow_add hJ, Real.rpow_mul hJ.le m 2,
      Real.rpow_two]
  set a := jbr ξ ^ m with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hJ _
  have hf' : ‖f ξ‖ = ‖p ξ‖ * ‖u ξ‖ := by rw [← hPu, norm_mul]
  have hkey : a ^ 2 ≤ (C₀⁻¹) ^ 2 * ‖p ξ‖ ^ 2 := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith [hb, mul_pos hC₀ ha0]
  have hs0 : 0 ≤ jbr ξ ^ (2 * s) := Real.rpow_nonneg hJ.le _
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hJ.le _) (sq_nonneg _)), hpow, hf']
  calc jbr ξ ^ (2 * s) * a ^ 2 * ‖u ξ‖ ^ 2
      ≤ jbr ξ ^ (2 * s) * ((C₀⁻¹) ^ 2 * ‖p ξ‖ ^ 2) * ‖u ξ‖ ^ 2 := by gcongr
    _ = (C₀⁻¹) ^ 2 * (jbr ξ ^ (2 * s) * (‖p ξ‖ * ‖u ξ‖) ^ 2) := by ring

end TorusPsiDO
