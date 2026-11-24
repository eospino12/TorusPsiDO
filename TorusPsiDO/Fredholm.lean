import TorusPsiDO.L2Operators
import TorusPsiDO.Elliptic
import TorusPsiDO.Fourier
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theorem 3.0.4: `(-Δ)^{ν/2} + Q(x)` is Fredholm `Hˢ(𝕋ⁿ) → H^{s-ν}(𝕋ⁿ)`

## Setting

* By Definition 2.0.3 of the thesis, the toroidal Fourier transform maps `C^∞(𝕋ⁿ)` onto the
  Schwartz space `S(ℤⁿ)` of rapidly decreasing sequences (Definition 2.0.1).  We therefore
  describe `Q ∈ C^∞(𝕋ⁿ)` by its Fourier coefficients `q = Q̂ ∈ S(ℤⁿ)`
  (`IsRapidlyDecreasing q`).  Multiplication by `Q` acts on Fourier coefficients by convolution
  with `q` (`mFourierCoeff_mul_mFourier`: `(Q e_η)^(ξ) = Q̂(ξ - η)`).
* `Hˢ(𝕋ⁿ)` is identified with `ℓ²(ℤⁿ)` through the unitary map `u ↦ (⟨ξ⟩ˢ û(ξ))_ξ`
  (`inSobolev_iff_memℓp`).  In these coordinates, `T = (-Δ)^{ν/2} + Q : Hˢ → H^{s-ν}` is the
  operator `sobolevOp ν q s : ℓ² → ℓ²` with
  `(sobolevOp v)(ξ) = ⟨ξ⟩^{s-ν} ((2π|ξ|)^ν ⟨ξ⟩^{-s} v(ξ) + ∑_η q(ξ-η) ⟨η⟩^{-s} v(η))`
  (`sobolevOp_apply`).

## Main result

`isFredholm_sobolevOp`: for `ν > 0`, `q ∈ S(ℤⁿ)` and every `s ∈ ℝ`, `sobolevOp ν q s` is a
Fredholm operator (`ContinuousLinearMap.IsFredholm` from Mathlib).

## Proof

The thesis cites Ruzhansky–Turunen, Thm. 4.9.17 (elliptic ⟹ Fredholm), which uses the full
symbolic calculus.  For this operator there is a shorter argument, which is the one formalized:
`T = A + ι ∘ (M_Q - I)`, where
* `A = (-Δ)^{ν/2} + 1 : Hˢ → H^{s-ν}` is invertible (its symbol `(2π|ξ|)^ν + 1 ≍ ⟨ξ⟩^ν`);
* `M_Q : Hˢ → Hˢ` is bounded, by Peetre's inequality and the Schur bound of `L2Operators.lean`;
* `ι : Hˢ ↪ H^{s-ν}` is a norm limit of finite-rank operators (Rellich), since `⟨ξ⟩^{-ν} → 0`.
So `T = A (I + E + F)` with `‖E‖ < 1` and `F` of finite rank, which is Fredholm.
-/

open Finset Filter Topology UnitAddTorus

namespace TorusPsiDO

variable {n : ℕ}

/-! ### Peetre's inequality -/

lemma jbr_neg (ξ : Fin n → ℤ) : jbr (-ξ) = jbr ξ := by simp [jbr]

/-- `⟨ξ⟩ ≤ √2 ⟨ξ - η⟩ ⟨η⟩`. -/
lemma jbr_le_sqrt2_mul (ξ η : Fin n → ℤ) : jbr ξ ≤ √2 * jbr (ξ - η) * jbr η := by
  have hA := sum_sq_nonneg (ξ - η)
  have hB := sum_sq_nonneg η
  have hcoord : ∑ i, ((ξ i : ℤ) : ℝ) ^ 2 ≤
      2 * ∑ i, (((ξ - η) i : ℤ) : ℝ) ^ 2 + 2 * ∑ i, ((η i : ℤ) : ℝ) ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    simp only [Pi.sub_apply, Int.cast_sub]
    nlinarith [sq_nonneg ((ξ i : ℝ) - 2 * η i)]
  have h1 : jbr ξ ^ 2 ≤ (√2 * jbr (ξ - η) * jbr η) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), jbr_sq, jbr_sq, jbr_sq]
    nlinarith [mul_nonneg hA hB]
  have h2 : 0 ≤ √2 * jbr (ξ - η) * jbr η :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (jbr_pos _).le) (jbr_pos _).le
  exact (pow_le_pow_iff_left₀ (jbr_pos ξ).le h2 two_ne_zero).mp h1

/-- **Peetre's inequality.** `⟨ξ⟩ˢ ⟨η⟩^{-s} ≤ √2^{|s|} ⟨ξ - η⟩^{|s|}`. -/
lemma weight_ratio_le (s : ℝ) (ξ η : Fin n → ℤ) :
    jbr ξ ^ s * jbr η ^ (-s) ≤ √2 ^ |s| * jbr (ξ - η) ^ |s| := by
  have hξ := jbr_pos ξ
  have hη := jbr_pos η
  have hd := jbr_pos (ξ - η)
  have h2 := Real.sqrt_nonneg 2
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    have h1 : jbr ξ ^ s ≤ (√2 * jbr (ξ - η) * jbr η) ^ s :=
      Real.rpow_le_rpow hξ.le (jbr_le_sqrt2_mul ξ η) hs
    rw [Real.mul_rpow (mul_nonneg h2 hd.le) hη.le, Real.mul_rpow h2 hd.le] at h1
    have he : jbr η ^ s * jbr η ^ (-s) = 1 := by
      rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero]
    calc jbr ξ ^ s * jbr η ^ (-s)
        ≤ (√2 ^ s * jbr (ξ - η) ^ s * jbr η ^ s) * jbr η ^ (-s) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hη.le _)
      _ = √2 ^ s * jbr (ξ - η) ^ s := by rw [mul_assoc, he, mul_one]
  · rw [abs_of_neg hs]
    have h1 : jbr η ^ (-s) ≤ (√2 * jbr (η - ξ) * jbr ξ) ^ (-s) :=
      Real.rpow_le_rpow hη.le (jbr_le_sqrt2_mul η ξ) (by linarith)
    rw [show η - ξ = -(ξ - η) by abel, jbr_neg, Real.mul_rpow (mul_nonneg h2 hd.le) hξ.le,
      Real.mul_rpow h2 hd.le] at h1
    have he : jbr ξ ^ (-s) * jbr ξ ^ s = 1 := by
      rw [← Real.rpow_add hξ, neg_add_cancel, Real.rpow_zero]
    calc jbr ξ ^ s * jbr η ^ (-s)
        ≤ jbr ξ ^ s * (√2 ^ (-s) * jbr (ξ - η) ^ (-s) * jbr ξ ^ (-s)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hξ.le _)
      _ = √2 ^ (-s) * jbr (ξ - η) ^ (-s) := by rw [mul_comm, mul_assoc, he, mul_one]

/-! ### Definition 2.0.1: the Schwartz space `S(ℤⁿ)` -/

/-- **Definition 2.0.1.** `φ ∈ S(ℤⁿ)`: for every `M` there is `C` with `|φ(ξ)| ≤ C ⟨ξ⟩^{-M}`. -/
def IsRapidlyDecreasing (φ : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ M : ℝ, ∃ C : ℝ, ∀ ξ, ‖φ ξ‖ ≤ C * jbr ξ ^ (-M)

lemma summable_int_inv_one_add_sq : Summable fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun m hm => ?_
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hm ⊢
  by_contra h0
  apply hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast h0
  have hpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ hpos (by linarith)

lemma summable_prod_inv : ∀ n : ℕ,
    Summable fun ξ : Fin n → ℤ => ∏ i, (1 + ((ξ i : ℤ) : ℝ) ^ 2)⁻¹
  | 0 => by
    haveI : Finite (Fin 0 → ℤ) := Finite.of_subsingleton
    exact Summable.of_finite
  | n + 1 => by
    have h := Summable.mul_of_nonneg summable_int_inv_one_add_sq (summable_prod_inv n)
      (fun m => by positivity) (fun ξ => prod_nonneg fun i _ => by positivity)
    refine ((Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff
      (f := fun ξ : Fin (n + 1) → ℤ => ∏ i, (1 + ((ξ i : ℤ) : ℝ) ^ 2)⁻¹)).mp ?_
    refine h.congr fun x => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ] <;> ring

/-- `∑_{ξ ∈ ℤⁿ} ⟨ξ⟩^{-2n} < ∞`. -/
lemma summable_jbr_rpow_neg : Summable fun ξ : Fin n → ℤ => jbr ξ ^ (-(2 * n : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun ξ => Real.rpow_nonneg (jbr_pos ξ).le _) (fun ξ => ?_)
    (summable_prod_inv n)
  have hS := sum_sq_nonneg ξ
  have hpow : jbr ξ ^ (2 * n : ℝ) = (1 + ∑ i, ((ξ i : ℤ) : ℝ) ^ 2) ^ n := by
    rw [show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
      jbr_sq]
  have hprod : ∏ i, (1 + ((ξ i : ℤ) : ℝ) ^ 2) ≤ (1 + ∑ i, ((ξ i : ℤ) : ℝ) ^ 2) ^ n := by
    calc ∏ i, (1 + ((ξ i : ℤ) : ℝ) ^ 2) ≤ ∏ _i : Fin n, (1 + ∑ i, ((ξ i : ℤ) : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => by
            have := single_le_sum (f := fun i => ((ξ i : ℤ) : ℝ) ^ 2)
              (fun _ _ => sq_nonneg _) (mem_univ i)
            linarith)
      _ = _ := by simp
  rw [Real.rpow_neg (jbr_pos ξ).le, hpow, prod_inv_distrib]
  exact inv_anti₀ (prod_pos fun i _ => by positivity) hprod

/-- Sequences in `S(ℤⁿ)` are summable against every weight `⟨ξ⟩^t`. -/
theorem IsRapidlyDecreasing.summable_weighted {φ : (Fin n → ℤ) → ℂ}
    (h : IsRapidlyDecreasing φ) (t : ℝ) : Summable fun k => jbr k ^ t * ‖φ k‖ := by
  obtain ⟨C, hC⟩ := h (t + 2 * n)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Real.rpow_nonneg (jbr_pos k).le _) (norm_nonneg _)) (fun k => ?_)
    (summable_jbr_rpow_neg.mul_left C)
  calc jbr k ^ t * ‖φ k‖ ≤ jbr k ^ t * (C * jbr k ^ (-(t + 2 * n))) :=
        mul_le_mul_of_nonneg_left (hC k) (Real.rpow_nonneg (jbr_pos k).le _)
    _ = C * jbr k ^ (-(2 * n : ℝ)) := by
        rw [mul_left_comm, ← Real.rpow_add (jbr_pos k)]
        congr 2; ring

/-! ### Sobolev coordinates -/

/-- `u ∈ Hˢ(𝕋ⁿ)` iff `(⟨ξ⟩ˢ û(ξ))_ξ ∈ ℓ²(ℤⁿ)`: this is the identification `Hˢ ≅ ℓ²`. -/
theorem inSobolev_iff_memℓp (s : ℝ) (u : (Fin n → ℤ) → ℂ) :
    InSobolev s u ↔ Memℓp (fun ξ => ((jbr ξ ^ s : ℝ) : ℂ) * u ξ) 2 := by
  rw [memℓp_two_iff, InSobolev]
  have h : ∀ ξ, ‖((jbr ξ ^ s : ℝ) : ℂ) * u ξ‖ ^ 2 = jbr ξ ^ (2 * s) * ‖u ξ‖ ^ 2 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _),
      mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (jbr_pos ξ).le]
    norm_num
    left; ring_nf
  simp_rw [h]

/-- Multiplication by `Q` acts on Fourier coefficients by convolution with `Q̂`:
`(Q e_η)^(ξ) = Q̂(ξ - η)`. -/
theorem mFourierCoeff_mul_mFourier (Q : UnitAddTorus (Fin n) → ℂ) (η ξ : Fin n → ℤ) :
    mFourierCoeff (fun t => Q t * mFourier η t) ξ = mFourierCoeff Q (ξ - η) := by
  simp only [mFourierCoeff]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, show -(ξ - η) = -ξ + η by abel, mFourier_add]
  ring

/-! ### The operator of Theorem 3.0.4 in Sobolev coordinates -/

section Operator

variable (ν : ℝ) (hν : 0 < ν) (q : (Fin n → ℤ) → ℂ) (hq : IsRapidlyDecreasing q) (s : ℝ)

/-- The symbol `(2π|ξ|)^ν` of `(-Δ)^{ν/2}`. -/
noncomputable def pSym (ξ : Fin n → ℤ) : ℝ := (2 * Real.pi * normZ ξ) ^ ν

lemma pSym_nonneg (ξ : Fin n → ℤ) : 0 ≤ pSym ν ξ :=
  Real.rpow_nonneg (by have := normZ_nonneg ξ; positivity) _

include hν in
lemma jbr_rpow_neg_le_one (ξ : Fin n → ℤ) : jbr ξ ^ (-ν) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_jbr ξ) (by linarith)

include hν in
lemma jbr_rpow_neg_mul_pSym_le (ξ : Fin n → ℤ) :
    jbr ξ ^ (-ν) * pSym ν ξ ≤ (2 * Real.pi) ^ ν := by
  have hj := jbr_pos ξ
  have hp : pSym ν ξ ≤ (2 * Real.pi) ^ ν * jbr ξ ^ ν := by
    rw [pSym, ← Real.mul_rpow (by positivity) hj.le]
    exact Real.rpow_le_rpow (by have := normZ_nonneg ξ; positivity)
      (mul_le_mul_of_nonneg_left (normZ_le_jbr ξ) (by positivity)) hν.le
  have he : jbr ξ ^ (-ν) * jbr ξ ^ ν = 1 := by
    rw [← Real.rpow_add hj, neg_add_cancel, Real.rpow_zero]
  calc jbr ξ ^ (-ν) * pSym ν ξ ≤ jbr ξ ^ (-ν) * ((2 * Real.pi) ^ ν * jbr ξ ^ ν) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hj.le _)
    _ = (2 * Real.pi) ^ ν := by rw [mul_left_comm, he, mul_one]

/-- The kernel bound `g(k) = √2^{|s|} ⟨k⟩^{|s|} |q(k)|`. -/
noncomputable def gQ (k : Fin n → ℤ) : ℝ := √2 ^ |s| * (jbr k ^ |s| * ‖q k‖)

lemma gQ_nonneg (k : Fin n → ℤ) : 0 ≤ gQ q s k :=
  mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (mul_nonneg (Real.rpow_nonneg (jbr_pos k).le _) (norm_nonneg _))

include hq in
lemma gQ_summable : Summable (gQ q s) := (hq.summable_weighted |s|).mul_left _

/-- The matrix of multiplication by `Q` in `Hˢ`-coordinates: `⟨ξ⟩ˢ q(ξ - η) ⟨η⟩^{-s}`. -/
noncomputable def mQ (ξ η : Fin n → ℤ) : ℂ := ((jbr ξ ^ s * jbr η ^ (-s) : ℝ) : ℂ) * q (ξ - η)

lemma norm_mQ_le (ξ η : Fin n → ℤ) : ‖mQ q s ξ η‖ ≤ gQ q s (ξ - η) := by
  rw [mQ, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _) (Real.rpow_nonneg (jbr_pos η).le _)), gQ,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_ratio_le s ξ η) (norm_nonneg _)

/-- Multiplication by `Q` as a bounded operator `Hˢ → Hˢ` (in `ℓ²` coordinates). -/
noncomputable def mulQ : L2 n →L[ℂ] L2 n :=
  kerL2 (gQ q s) (gQ_nonneg q s) (gQ_summable q hq s) (mQ q s) (norm_mQ_le q s)

/-- The diagonal operator `⟨ξ⟩^{-ν} (2π|ξ|)^ν`. -/
noncomputable def diagP : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => ((jbr ξ ^ (-ν) * pSym ν ξ : ℝ) : ℂ)) ((2 * Real.pi) ^ ν)
    (by positivity) (fun ξ => by
      rw [Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _) (pSym_nonneg ν ξ))]
      exact jbr_rpow_neg_mul_pSym_le ν hν ξ)

/-- The inclusion `Hˢ ↪ H^{s-ν}` in `ℓ²` coordinates: multiplication by `⟨ξ⟩^{-ν}`. -/
noncomputable def incl : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => ((jbr ξ ^ (-ν) : ℝ) : ℂ)) 1 zero_le_one (fun ξ => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _)]
    exact jbr_rpow_neg_le_one ν hν ξ)

/-- **The operator of Theorem 3.0.4**, `(-Δ)^{ν/2} + Q : Hˢ(𝕋ⁿ) → H^{s-ν}(𝕋ⁿ)`, written in the
coordinates `Hˢ ≅ ℓ²`, `H^{s-ν} ≅ ℓ²`. -/
noncomputable def sobolevOp : L2 n →L[ℂ] L2 n :=
  diagP ν hν + incl ν hν ∘L mulQ q hq s

/-- The coordinate formula: `sobolevOp = W_{s-ν} ∘ ((-Δ)^{ν/2} + Q) ∘ W_s⁻¹`, where
`W_t u = (⟨ξ⟩ᵗ û(ξ))_ξ` and `(Q u)^ = q ∗ û`. -/
theorem sobolevOp_apply (v : L2 n) (ξ : Fin n → ℤ) :
    sobolevOp ν hν q hq s v ξ = ((jbr ξ ^ (s - ν) : ℝ) : ℂ) *
      ((pSym ν ξ : ℂ) * ((jbr ξ ^ (-s) : ℝ) : ℂ) * v ξ +
        ∑' η, q (ξ - η) * (((jbr η ^ (-s) : ℝ) : ℂ) * v η)) := by
  have hj := jbr_pos ξ
  have hsum : ∑' η, mQ q s ξ η * v η =
      ((jbr ξ ^ s : ℝ) : ℂ) * ∑' η, q (ξ - η) * (((jbr η ^ (-s) : ℝ) : ℂ) * v η) := by
    rw [← tsum_mul_left]
    congr 1; funext η
    simp only [mQ, Complex.ofReal_mul]
    ring
  have e1 : jbr ξ ^ (-ν) = jbr ξ ^ (s - ν) * jbr ξ ^ (-s) := by
    rw [← Real.rpow_add hj]; congr 1; ring
  have e2 : jbr ξ ^ (-ν) * jbr ξ ^ s = jbr ξ ^ (s - ν) := by
    rw [← Real.rpow_add hj]; congr 1; ring
  have e1c : ((jbr ξ ^ (-ν) : ℝ) : ℂ) = ((jbr ξ ^ (s - ν) : ℝ) : ℂ) * ((jbr ξ ^ (-s) : ℝ) : ℂ) :=
    by exact_mod_cast e1
  have e2c : ((jbr ξ ^ (-ν) : ℝ) : ℂ) * ((jbr ξ ^ s : ℝ) : ℂ) = ((jbr ξ ^ (s - ν) : ℝ) : ℂ) :=
    by exact_mod_cast e2
  simp only [sobolevOp, diagP, incl, mulQ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, lp.coeFn_add, Pi.add_apply, diagL2_apply, kerL2_apply,
    hsum, Complex.ofReal_mul]
  linear_combination ((pSym ν ξ : ℂ) * v ξ) * e1c +
    (∑' η, q (ξ - η) * (((jbr η ^ (-s) : ℝ) : ℂ) * v η)) * e2c

end Operator

/-! ### The Fredholm property -/

section Fredholm

variable (ν : ℝ) (hν : 0 < ν) (q : (Fin n → ℤ) → ℂ) (hq : IsRapidlyDecreasing q) (s : ℝ)

/-- The symbol of `A = (-Δ)^{ν/2} + 1` in Sobolev coordinates. -/
noncomputable def aSym (ξ : Fin n → ℤ) : ℝ := jbr ξ ^ (-ν) * (pSym ν ξ + 1)

include hν in
lemma jbr_rpow_le_pSym_add_one (ξ : Fin n → ℤ) : jbr ξ ^ ν ≤ pSym ν ξ + 1 := by
  by_cases h1 : 1 ≤ normZ ξ
  · have h0 := normZ_nonneg ξ
    have : jbr ξ ^ ν ≤ pSym ν ξ := by
      rw [pSym]
      refine Real.rpow_le_rpow (jbr_pos ξ).le ((jbr_le_two_normZ h1).trans ?_) hν.le
      nlinarith [Real.two_le_pi]
    linarith
  · push Not at h1
    have hz : ∀ i, ξ i = 0 := by
      intro i
      have h := (abs_coord_le_normZ ξ i).trans_lt h1
      have : |ξ i| < 1 := by exact_mod_cast (show (|(ξ i : ℝ)|) < 1 from h)
      exact Int.abs_lt_one_iff.mp this
    have hj : jbr ξ = 1 := by simp [jbr, hz]
    rw [hj, Real.one_rpow]
    linarith [pSym_nonneg ν ξ]

include hν in
lemma one_le_aSym (ξ : Fin n → ℤ) : 1 ≤ aSym ν ξ := by
  have hj := jbr_pos ξ
  have he : jbr ξ ^ (-ν) * jbr ξ ^ ν = 1 := by
    rw [← Real.rpow_add hj, neg_add_cancel, Real.rpow_zero]
  calc (1 : ℝ) = jbr ξ ^ (-ν) * jbr ξ ^ ν := he.symm
    _ ≤ jbr ξ ^ (-ν) * (pSym ν ξ + 1) := mul_le_mul_of_nonneg_left
        (jbr_rpow_le_pSym_add_one ν hν ξ) (Real.rpow_nonneg hj.le _)

include hν in
lemma aSym_le (ξ : Fin n → ℤ) : aSym ν ξ ≤ (2 * Real.pi) ^ ν + 1 := by
  rw [aSym, mul_add, mul_one]
  linarith [jbr_rpow_neg_mul_pSym_le ν hν ξ, jbr_rpow_neg_le_one ν hν ξ]

/-- `A = (-Δ)^{ν/2} + 1 : Hˢ → H^{s-ν}`. -/
noncomputable def opA : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => ((aSym ν ξ : ℝ) : ℂ)) ((2 * Real.pi) ^ ν + 1) (by positivity) (fun ξ => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [one_le_aSym ν hν ξ])]
    exact aSym_le ν hν ξ)

/-- `A⁻¹`. -/
noncomputable def opAinv : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => (((aSym ν ξ)⁻¹ : ℝ) : ℂ)) 1 zero_le_one (fun ξ => by
    have h := one_le_aSym ν hν ξ
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ h)

include hν in
lemma aSym_ne_zero (ξ : Fin n → ℤ) : ((aSym ν ξ : ℝ) : ℂ) ≠ 0 := by
  have := one_le_aSym ν hν ξ
  exact_mod_cast (show aSym ν ξ ≠ 0 by linarith)

lemma opA_comp_opAinv : opA ν hν ∘L opAinv ν hν = (1 : L2 n →L[ℂ] L2 n) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun ξ => ?_)
  simp only [opA, opAinv, ContinuousLinearMap.comp_apply, diagL2_apply,
    ContinuousLinearMap.one_apply, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (aSym_ne_zero ν hν ξ), one_mul]

lemma opAinv_comp_opA : opAinv ν hν ∘L opA ν hν = (1 : L2 n →L[ℂ] L2 n) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun ξ => ?_)
  simp only [opA, opAinv, ContinuousLinearMap.comp_apply, diagL2_apply,
    ContinuousLinearMap.one_apply, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (aSym_ne_zero ν hν ξ), one_mul]

lemma opA_isInvertible : (opA (n := n) ν hν).IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse (opA ν hν) (opAinv ν hν)
    (fun v => by
      have := congrArg (fun T : L2 n →L[ℂ] L2 n => T v) (opAinv_comp_opA ν hν)
      simpa using this)
    (fun v => by
      have := congrArg (fun T : L2 n →L[ℂ] L2 n => T v) (opA_comp_opAinv ν hν)
      simpa using this), rfl⟩

/-- `sobolevOp = A + ι ∘ (M_Q - I)`. -/
lemma sobolevOp_eq :
    sobolevOp ν hν q hq s = opA ν hν + incl ν hν ∘L (mulQ q hq s - 1) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun ξ => ?_)
  simp only [sobolevOp, diagP, incl, opA, aSym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply, diagL2_apply, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one]
  ring

/-- For `R`, the finite set `{ξ : |ξ| < R}`. -/
noncomputable def ballSet (R : ℝ) : Finset (Fin n → ℤ) := (finite_normZ_lt R).toFinset

lemma mem_ballSet {R : ℝ} {ξ : Fin n → ℤ} : ξ ∈ ballSet R ↔ normZ ξ < R := by
  simp [ballSet]

/-- The low-frequency part `ι_R` of the inclusion (finite rank). -/
noncomputable def inclLow (R : ℝ) : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => if jbr ξ < R then ((jbr ξ ^ (-ν) : ℝ) : ℂ) else 0) 1 zero_le_one (fun ξ => by
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _)]
      exact jbr_rpow_neg_le_one ν hν ξ
    · simp)

/-- The high-frequency part of the inclusion, of norm `≤ ε` when `⟨ξ⟩^{-ν} ≤ ε` for
`⟨ξ⟩ ≥ R`. -/
noncomputable def inclHigh (R ε : ℝ) (hε : 0 ≤ ε) (hR : ∀ ξ : Fin n → ℤ, R ≤ jbr ξ →
    jbr ξ ^ (-ν) ≤ ε) : L2 n →L[ℂ] L2 n :=
  diagL2 (fun ξ => if jbr ξ < R then 0 else ((jbr ξ ^ (-ν) : ℝ) : ℂ)) ε hε (fun ξ => by
    split_ifs with h
    · simpa using hε
    · push Not at h
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jbr_pos ξ).le _)]
      exact hR ξ h)

lemma incl_eq_low_add_high (R ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ ξ : Fin n → ℤ, R ≤ jbr ξ → jbr ξ ^ (-ν) ≤ ε) :
    incl ν hν = inclLow ν hν R + inclHigh ν R ε hε hR := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun ξ => ?_)
  simp only [incl, inclLow, inclHigh, ContinuousLinearMap.add_apply, lp.coeFn_add,
    Pi.add_apply, diagL2_apply]
  split_ifs <;> ring

/-- `ι_R` has finite rank: its range lies in the span of the `e_ξ`, `|ξ| < R`. -/
lemma inclLow_hasFiniteRange (R : ℝ) (B : L2 n →L[ℂ] L2 n) :
    LinearMap.HasFiniteRange ((inclLow ν hν R ∘L B : L2 n →L[ℂ] L2 n) : L2 n →ₗ[ℂ] L2 n) := by
  set S := ballSet (n := n) R
  set V : Submodule ℂ (L2 n) :=
    Submodule.span ℂ ((fun ξ => (lp.single 2 ξ (1 : ℂ) : L2 n)) '' (S : Set (Fin n → ℤ)))
  have hV : V.FG := Submodule.fg_span ((Finset.finite_toSet S).image _)
  refine Submodule.FG.of_le hV ?_
  rintro _ ⟨w, rfl⟩
  set u := inclLow ν hν R (B w)
  have hu : u = ∑ ξ ∈ S, u ξ • lp.single 2 ξ (1 : ℂ) := by
    refine lp.ext (funext fun η => ?_)
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq]
    split_ifs with hη
    · rfl
    · have h1 : R ≤ normZ η := by
        rw [mem_ballSet] at hη; push Not at hη; exact hη
      have h2 : ¬ jbr η < R := by linarith [normZ_le_jbr η]
      simp [u, inclLow, diagL2_apply, h2]
  change u ∈ V
  rw [hu]
  refine Submodule.sum_mem _ fun ξ hξ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hξ)

/-- **Theorem 3.0.4 (Fredholm property).** For `ν > 0`, `Q ∈ C^∞(𝕋ⁿ)` (i.e. `Q̂ ∈ S(ℤⁿ)`)
and every `s ∈ ℝ`, the operator `(-Δ)^{ν/2} + Q : Hˢ(𝕋ⁿ) → H^{s-ν}(𝕋ⁿ)` is Fredholm. -/
theorem isFredholm_sobolevOp : (sobolevOp (n := n) ν hν q hq s).IsFredholm := by
  set B : L2 n →L[ℂ] L2 n := mulQ q hq s - 1 with hB
  set ε : ℝ := 1 / (2 * (‖B‖ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  -- choose `R` with `⟨ξ⟩^{-ν} ≤ ε` for `⟨ξ⟩ ≥ R`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → x ^ (-ν) ≤ ε := by
    have := (tendsto_rpow_neg_atTop hν).eventually (ge_mem_nhds hε)
    exact Filter.eventually_atTop.mp this
  have hR' : ∀ ξ : Fin n → ℤ, R ≤ jbr ξ → jbr ξ ^ (-ν) ≤ ε := fun ξ h => hR _ h
  set A := opA (n := n) ν hν
  set Ai := opAinv (n := n) ν hν
  set E := Ai ∘L (inclHigh ν R ε hε.le hR' ∘L B) with hE
  set F := Ai ∘L (inclLow ν hν R ∘L B) with hF
  -- `‖E‖ < 1`
  have hEn : ‖E‖ < 1 := by
    have h1 : ‖Ai‖ ≤ 1 := norm_diagL2_le _ _ _ _
    have h2 : ‖inclHigh ν R ε hε.le hR'‖ ≤ ε := norm_diagL2_le _ _ _ _
    calc ‖E‖ ≤ ‖Ai‖ * (‖inclHigh ν R ε hε.le hR'‖ * ‖B‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (ε * ‖B‖) := by gcongr
      _ < 1 := by
          rw [one_mul, hεdef]
          have hb := norm_nonneg B
          rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
          linarith
  -- `I + E` is invertible (Neumann series)
  have hU : (1 + E).IsInvertible := by
    set u := Units.oneSub (-E) (by rwa [norm_neg])
    have hu : (u : L2 n →L[ℂ] L2 n) = 1 + E := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℂ (L2 n) u, ?_⟩
    rw [← hu]
    rfl
  -- `F` has finite rank
  have hFfin : LinearMap.HasFiniteRange (F : L2 n →ₗ[ℂ] L2 n) :=
    (inclLow_hasFiniteRange ν hν R B).comp_left (Ai : L2 n →ₗ[ℂ] L2 n)
  have hfred : (1 + E + F).IsFredholm := hU.isFredholm.add_hasFiniteRange hFfin
  -- `sobolevOp = A ∘ (I + E + F)`
  have hdecomp : sobolevOp ν hν q hq s = A ∘L (1 + E + F) := by
    rw [sobolevOp_eq, incl_eq_low_add_high ν hν R ε hε.le hR']
    refine ContinuousLinearMap.ext fun v => ?_
    have hAAi : ∀ w, A (Ai w) = w := fun w => by
      have := congrArg (fun T : L2 n →L[ℂ] L2 n => T w) (opA_comp_opAinv (n := n) ν hν)
      simpa using this
    simp only [E, F, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, map_add, hAAi]
    abel
  rw [hdecomp]
  exact (opA_isInvertible ν hν).isFredholm.comp hfred

end Fredholm

end TorusPsiDO
