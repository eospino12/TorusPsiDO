import TorusPsiDO.Symbols
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Periodic functions and the toroidal quantization (Thesis, §1.3 and Chapter 2)

* `ePow ξ x = e^{2πi x·ξ}`, the canonical trigonometric polynomials (Remark 2.0.16).
* Definition 1.3.1 and Example 1.3.2: trigonometric polynomials are `1`-periodic.
* Definition 2.0.15: the toroidal quantization `Op(a) f(x) = ∑_ξ e^{2πi x·ξ} a(x, ξ) f̂(ξ)`,
  on trigonometric polynomials `f = ∑_{ξ ∈ S} f̂(ξ) e_ξ`.  (On the torus side, the fact that
  `f̂(ξ)` really is the toroidal Fourier coefficient of `f` is `TorusPsiDO.mFourierCoeff_trigPoly`
  in `Fourier.lean`.)
* Remark 2.0.16: the symbol is recovered as `a(x, ξ) = e^{-2πi x·ξ} (Op(a) e_ξ)(x)`.
* Page 35: translations act on Fourier coefficients by `(T_h f)^(ξ) = e^{2πi h·ξ} f̂(ξ)`.
* Corollary 2.0.26: Fourier multipliers commute with translations; in particular `-Δ`.
* Example 2.0.27: the symbol `2^ν π^ν |ξ|^ν = (2π|ξ|)^ν` of the fractional Laplacian.
* Example 2.0.28: `Op(|ξ|² + V(x)) f = Op(|ξ|²) f + V f`.
* Example 3.0.3 / page 44: the symbol of `-Δ` is `4π²|ξ|²`, i.e. `Op(4π²|ξ|²) f = -Δ f`.
* Example 2.0.30: `Op((1 + sin 2πx)√(1+ξ²)) cos(2πx) = √2 (1 + sin 2πx) cos(2πx)`.
-/

open Complex Finset Real

namespace TorusPsiDO

variable {n : ℕ}

/-- The pairing `x · ξ` between `x ∈ ℝⁿ` and `ξ ∈ ℤⁿ`. -/
def dot (x : Fin n → ℝ) (ξ : Fin n → ℤ) : ℝ := ∑ i, x i * ξ i

/-- `e_ξ(x) = e^{2πi x·ξ}`. -/
noncomputable def ePow (ξ : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (2 * π * I * (dot x ξ : ℂ))

lemma dot_add_left (x y : Fin n → ℝ) (ξ : Fin n → ℤ) : dot (x + y) ξ = dot x ξ + dot y ξ := by
  simp [dot, add_mul, sum_add_distrib]

lemma dot_add_right (x : Fin n → ℝ) (ξ η : Fin n → ℤ) : dot x (ξ + η) = dot x ξ + dot x η := by
  simp [dot, mul_add, sum_add_distrib]

lemma dot_neg_right (x : Fin n → ℝ) (ξ : Fin n → ℤ) : dot x (-ξ) = -dot x ξ := by
  simp [dot, sum_neg_distrib]

lemma dot_zero_right (x : Fin n → ℝ) : dot x 0 = 0 := by simp [dot]

lemma dot_toR (k ξ : Fin n → ℤ) : dot (toR k) ξ = ((∑ i, k i * ξ i : ℤ) : ℝ) := by
  simp [dot, toR]

lemma ePow_add (ξ : Fin n → ℤ) (x y : Fin n → ℝ) : ePow ξ (x + y) = ePow ξ x * ePow ξ y := by
  rw [ePow, ePow, ePow, ← Complex.exp_add, dot_add_left]
  push_cast; ring_nf

lemma ePow_add_freq (ξ η : Fin n → ℤ) (x : Fin n → ℝ) :
    ePow (ξ + η) x = ePow ξ x * ePow η x := by
  rw [ePow, ePow, ePow, ← Complex.exp_add, dot_add_right]
  push_cast; ring_nf

lemma ePow_zero_freq (x : Fin n → ℝ) : ePow 0 x = 1 := by
  simp [ePow, dot_zero_right]

lemma ePow_neg_mul (ξ : Fin n → ℤ) (x : Fin n → ℝ) : ePow (-ξ) x * ePow ξ x = 1 := by
  rw [← ePow_add_freq, neg_add_cancel, ePow_zero_freq]

/-- `e_ξ` is `1`-periodic. -/
lemma ePow_periodic (ξ k : Fin n → ℤ) (x : Fin n → ℝ) : ePow ξ (x + toR k) = ePow ξ x := by
  rw [ePow_add]
  have : ePow ξ (toR k) = 1 := by
    rw [ePow, dot_toR]
    have := Complex.exp_int_mul_two_pi_mul_I (∑ i, k i * ξ i)
    rw [← this]; congr 1; push_cast; ring
  rw [this, mul_one]

lemma norm_ePow (ξ : Fin n → ℤ) (x : Fin n → ℝ) : ‖ePow ξ x‖ = 1 := by
  rw [ePow, show (2 * π * I * (dot x ξ : ℂ)) = ((2 * π * dot x ξ : ℝ) : ℂ) * I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### §1.3: periodic functions and trigonometric polynomials -/

/-- **Definition 1.3.1.** `f : ℝⁿ → ℂ` is `1`-periodic if `f(x + k) = f(x)` for `k ∈ ℤⁿ`. -/
def IsPeriodic (f : (Fin n → ℝ) → ℂ) : Prop := ∀ x (k : Fin n → ℤ), f (x + toR k) = f x

/-- The trigonometric polynomial `∑_{ξ ∈ S} c_ξ e^{2πi x·ξ}`. -/
noncomputable def trigPoly (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ ξ ∈ S, c ξ * ePow ξ x

/-- **Example 1.3.2.** Trigonometric polynomials are `1`-periodic. -/
theorem trigPoly_periodic (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    IsPeriodic (trigPoly S c) := by
  intro x k
  simp [trigPoly, ePow_periodic]

/-! ### Definition 2.0.15: the toroidal quantization -/

/-- **Definition 2.0.15.** `Op(a) f(x) = ∑_ξ e^{2πi x·ξ} a(x, ξ) f̂(ξ)` for the trigonometric
polynomial `f` with Fourier coefficients `f̂ = c` supported in `S`. -/
noncomputable def Op (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ ξ ∈ S, ePow ξ x * a x ξ * c ξ

/-- The symbol `1` quantizes to the identity. -/
theorem Op_one (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) :
    Op (fun _ _ => 1) S c = trigPoly S c := by
  funext x; simp [Op, trigPoly, mul_comm]

/-- The quantization is linear in the symbol. -/
theorem Op_add (a b : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) :
    Op (fun x ξ => a x ξ + b x ξ) S c x = Op a S c x + Op b S c x := by
  simp [Op, mul_add, add_mul, sum_add_distrib]

/-- The quantization is linear in the function. -/
theorem Op_add_right (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c d : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) :
    Op a S (c + d) x = Op a S c x + Op a S d x := by
  simp [Op, mul_add, sum_add_distrib]

/-- **Remark 2.0.16.** The symbol is recovered from the operator:
`a(x, ξ) = e^{-2πi x·ξ} (Op(a) e_ξ)(x)`. -/
theorem symbol_eq_of_Op (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) (ξ : Fin n → ℤ)
    (x : Fin n → ℝ) : a x ξ = ePow (-ξ) x * Op a {ξ} (fun _ => 1) x := by
  simp only [Op, sum_singleton, mul_one]
  rw [← mul_assoc, ePow_neg_mul, one_mul]

/-- `Op(a)` of a periodic symbol maps trigonometric polynomials to periodic functions. -/
theorem Op_periodic (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ)
    (ha : ∀ x ξ (k : Fin n → ℤ), a (x + toR k) ξ = a x ξ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) : IsPeriodic (Op a S c) := by
  intro x k
  simp [Op, ePow_periodic, ha]

/-! ### Translations and Fourier multipliers (pages 35–36) -/

/-- **Page 35.** `(T_h f)(x) = f(x + h)` acts on the Fourier coefficients by multiplication by
`e^{2πi h·ξ}`: `(T_h f)^(ξ) = e^{2πi h·ξ} f̂(ξ)`. -/
theorem trigPoly_translate (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x h : Fin n → ℝ) :
    trigPoly S c (x + h) = trigPoly S (fun ξ => ePow ξ h * c ξ) x := by
  simp only [trigPoly, ePow_add]
  refine sum_congr rfl fun ξ _ => by ring

/-- **Page 35.** `P(T_h f)(x) = ∑_ξ p(x, ξ) e^{2πi ξ·h} f̂(ξ) e^{2πi ξ·x}`. -/
theorem Op_translate (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) (x h : Fin n → ℝ) :
    Op a S (fun ξ => ePow ξ h * c ξ) x = ∑ ξ ∈ S, a x ξ * ePow ξ h * c ξ * ePow ξ x := by
  simp only [Op]
  refine sum_congr rfl fun ξ _ => by ring

/-- **Corollary 2.0.26.** A Fourier multiplier `F = Op(m)` (symbol independent of `x`) commutes
with every translation: `F(T_h a) = T_h(F a)`. -/
theorem multiplier_comm_translate (m : (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) (x h : Fin n → ℝ) :
    Op (fun _ ξ => m ξ) S (fun ξ => ePow ξ h * c ξ) x = Op (fun _ ξ => m ξ) S c (x + h) := by
  simp only [Op, ePow_add]
  refine sum_congr rfl fun ξ _ => by ring

/-- The symbol `4π²|ξ|²` of `-Δ` (Example 3.0.3). -/
noncomputable def lapSymbol (ξ : Fin n → ℤ) : ℂ := 4 * π ^ 2 * ∑ j, ((ξ j : ℂ)) ^ 2

lemma lapSymbol_eq (ξ : Fin n → ℤ) : lapSymbol ξ = ((4 * π ^ 2 * normZ ξ ^ 2 : ℝ) : ℂ) := by
  rw [normZ_sq, lapSymbol]; push_cast; rfl

/-- **Page 35.** `-Δ(T_h f) = T_h(-Δ f)`. -/
theorem lap_comm_translate (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x h : Fin n → ℝ) :
    Op (fun _ ξ => lapSymbol ξ) S (fun ξ => ePow ξ h * c ξ) x =
      Op (fun _ ξ => lapSymbol ξ) S c (x + h) :=
  multiplier_comm_translate _ S c x h

/-- **Example 2.0.28.** `(-Δ + V(x)) f = -Δ f + V(x) f`, at the level of symbols:
`Op(p(ξ) + V(x)) f = Op(p) f + V f`. -/
theorem Op_add_potential (p : (Fin n → ℤ) → ℂ) (V : (Fin n → ℝ) → ℂ)
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) :
    Op (fun x ξ => p ξ + V x) S c x = Op (fun _ ξ => p ξ) S c x + V x * trigPoly S c x := by
  rw [Op_add]
  congr 1
  simp only [Op, trigPoly, mul_sum]
  refine sum_congr rfl fun ξ _ => by ring

/-- **Example 2.0.27.** The symbol `2^ν π^ν |ξ|^ν` of `(-Δ)^{ν/2}` equals `(2π|ξ|)^ν`. -/
theorem fracLap_symbol (ν : ℝ) (ξ : Fin n → ℤ) :
    (2 : ℝ) ^ ν * π ^ ν * normZ ξ ^ ν = (2 * π * normZ ξ) ^ ν := by
  rw [Real.mul_rpow (by positivity) (normZ_nonneg ξ),
    Real.mul_rpow (by norm_num) Real.pi_pos.le]

/-! ### The symbol of `-Δ` (Example 3.0.3, page 44) -/

/-- The `j`-th unit vector of `ℝⁿ`. -/
def eR (j : Fin n) : Fin n → ℝ := Pi.single j 1

/-- The partial derivative `∂f/∂x_j (x) = d/dt f(x + t e_j) |_{t=0}`. -/
noncomputable def pd (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  deriv (fun t : ℝ => f (x + t • eR j)) 0

/-- The Laplacian `Δ f = ∑_j ∂²f/∂x_j²`. -/
noncomputable def lap (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ := ∑ j, pd j (pd j f) x

lemma dot_smul_eR (t : ℝ) (j : Fin n) (ξ : Fin n → ℤ) : dot (t • eR j) ξ = t * ξ j := by
  simp [dot, eR, Pi.single_apply]

lemma ePow_line (ξ : Fin n → ℤ) (y : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    ePow ξ (y + t • eR j) = ePow ξ y * Complex.exp ((2 * π * I * ξ j) * t) := by
  rw [ePow_add]
  congr 1
  rw [ePow, dot_smul_eR]
  push_cast; ring_nf

lemma hasDerivAt_ePow_line (ξ : Fin n → ℤ) (y : Fin n → ℝ) (j : Fin n) :
    HasDerivAt (fun t : ℝ => ePow ξ (y + t • eR j)) (2 * π * I * ξ j * ePow ξ y) 0 := by
  simp_rw [ePow_line]
  have h1 : HasDerivAt (fun t : ℝ => (2 * π * I * ξ j) * (t : ℂ)) (2 * π * I * ξ j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * π * I * (ξ j : ℂ))
  have h2 := (h1.cexp).const_mul (ePow ξ y)
  convert h2 using 1
  simp; ring

/-- Differentiating a trigonometric polynomial in `x_j` multiplies its coefficients by
`2πi ξ_j`. -/
theorem pd_trigPoly (S : Finset (Fin n → ℤ)) (d : (Fin n → ℤ) → ℂ) (j : Fin n) :
    pd j (fun y => ∑ ξ ∈ S, d ξ * ePow ξ y) =
      fun y => ∑ ξ ∈ S, (d ξ * (2 * π * I * ξ j)) * ePow ξ y := by
  funext y
  unfold pd
  have := HasDerivAt.sum (u := S) (A := fun ξ t => d ξ * ePow ξ (y + t • eR j))
    (fun ξ _ => (hasDerivAt_ePow_line ξ y j).const_mul (d ξ))
  have h2 : HasDerivAt (fun t : ℝ => ∑ ξ ∈ S, d ξ * ePow ξ (y + t • eR j))
      (∑ ξ ∈ S, d ξ * (2 * π * I * ξ j * ePow ξ y)) 0 := by
    convert this using 1
    funext t
    simp [Finset.sum_apply]
  show deriv (fun t : ℝ => ∑ ξ ∈ S, d ξ * ePow ξ (y + t • eR j)) 0 = _
  rw [h2.deriv]
  refine sum_congr rfl fun ξ _ => by ring

/-- **Example 3.0.3 / page 44.** On trigonometric polynomials, the operator with symbol
`4π²|ξ|²` is `-Δ`: `-Δ f(x) = ∑_ξ f̂(ξ) (2π|ξ|)² e_ξ(x)`. -/
theorem Op_lapSymbol (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) :
    Op (fun _ ξ => lapSymbol ξ) S c x = -lap (trigPoly S c) x := by
  have ht : trigPoly S c = fun y => ∑ ξ ∈ S, c ξ * ePow ξ y := rfl
  simp only [lap, ht, pd_trigPoly]
  rw [Finset.sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun ξ _ => ?_
  have h : ∀ j : Fin n, c ξ * (2 * π * I * ξ j) * (2 * π * I * ξ j) * ePow ξ x =
      -(4 * π ^ 2 * c ξ * ePow ξ x) * ((ξ j : ℂ)) ^ 2 := by
    intro j
    linear_combination (4 * π ^ 2 * ((ξ j : ℂ)) ^ 2 * c ξ * ePow ξ x) * I_sq
  simp_rw [h, ← mul_sum, lapSymbol]
  ring

/-! ### Example 2.0.30 -/

section Example2030

/-- The frequency `1 ∈ ℤ¹`. -/
def ξone : Fin 1 → ℤ := fun _ => 1

/-- `S = {1, -1}`. -/
def S30 : Finset (Fin 1 → ℤ) := {ξone, -ξone}

/-- `cos(2πx) = ½ e^{2πix} + ½ e^{-2πix}`: `f̂(±1) = 1/2`. -/
noncomputable def c30 : (Fin 1 → ℤ) → ℂ := fun _ => 1 / 2

/-- `σ(x, ξ) = (1 + sin 2πx) √(1 + ξ²)`. -/
noncomputable def σ30 (x : Fin 1 → ℝ) (ξ : Fin 1 → ℤ) : ℂ :=
  (((1 + Real.sin (2 * π * x 0)) * Real.sqrt (1 + ((ξ 0 : ℤ) : ℝ) ^ 2) : ℝ) : ℂ)

lemma ξone_ne : ξone ≠ -ξone := by
  intro h
  have := congrFun h 0
  simp [ξone] at this

lemma ePow_ξone (x : Fin 1 → ℝ) : ePow ξone x = Complex.exp (((2 * π * x 0 : ℝ) : ℂ) * I) := by
  simp only [ePow, dot, ξone, Fin.sum_univ_one]
  push_cast; ring_nf

lemma ePow_neg_ξone (x : Fin 1 → ℝ) :
    ePow (-ξone) x = Complex.exp (-((2 * π * x 0 : ℝ) : ℂ) * I) := by
  simp only [ePow, dot, ξone, Fin.sum_univ_one, Pi.neg_apply]
  push_cast; ring_nf

/-- **Example 2.0.30.** `f(x) = cos(2πx)` has Fourier coefficients `f̂(±1) = 1/2`. -/
theorem trigPoly_ex2030 (x : Fin 1 → ℝ) :
    trigPoly S30 c30 x = (Real.cos (2 * π * x 0) : ℂ) := by
  rw [trigPoly, S30, sum_pair ξone_ne, ePow_ξone, ePow_neg_ξone, Complex.exp_mul_I,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  simp only [c30]
  ring

/-- **Example 2.0.30.** `Op(σ) cos(2πx) = √2 (1 + sin 2πx) cos(2πx)`. -/
theorem Op_ex2030 (x : Fin 1 → ℝ) :
    Op σ30 S30 c30 x =
      ((Real.sqrt 2 * (1 + Real.sin (2 * π * x 0)) * Real.cos (2 * π * x 0) : ℝ) : ℂ) := by
  have h1 : σ30 x ξone = ((Real.sqrt 2 * (1 + Real.sin (2 * π * x 0)) : ℝ) : ℂ) := by
    simp only [σ30, ξone]; norm_num; ring
  have h2 : σ30 x (-ξone) = ((Real.sqrt 2 * (1 + Real.sin (2 * π * x 0)) : ℝ) : ℂ) := by
    simp only [σ30, ξone, Pi.neg_apply]; norm_num; ring
  have hop : Op σ30 S30 c30 x =
      ((Real.sqrt 2 * (1 + Real.sin (2 * π * x 0)) : ℝ) : ℂ) * trigPoly S30 c30 x := by
    simp only [Op, trigPoly, S30, sum_pair ξone_ne, h1, h2]
    ring
  rw [hop, trigPoly_ex2030]
  push_cast; ring

end Example2030

end TorusPsiDO
