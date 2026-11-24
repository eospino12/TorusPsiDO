import TorusPsiDO.Quantization
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier analysis on `ℝⁿ` and on `𝕋ⁿ` (Thesis, §1.4–§1.5)

On `ℝⁿ` (§1.4) we use Mathlib's Fourier transform `𝓕 f(ξ) = ∫ e^{-2πi x·ξ} f(x) dx`:

* Example 1.4.2: the Gaussian `e^{-πx²}` is its own Fourier transform.
* Proposition 1.4.6 (1): `‖f̂‖_∞ ≤ ‖f‖_{L¹}`.
* Theorem 1.4.8 (2): the Fourier inversion formula.
* Example 1.4.13: the test that shows that `e^{|x|²}` is not a tempered distribution.

On `𝕋ⁿ` (§1.5) we use Mathlib's `UnitAddTorus (Fin n) = (ℝ/ℤ)ⁿ`, its exponentials
`mFourier ξ` and Fourier coefficients `mFourierCoeff f ξ = ∫_{𝕋ⁿ} e^{-2πi x·ξ} f(x) dx`
(Definition 2.0.3):

* `mFourier_coe`: on representatives, `mFourier ξ` is the function `e^{2πi x·ξ}` used in
  `Quantization.lean`.
* Examples 1.5.3 and 1.5.4: the Fourier coefficients of `1` and of `e^{2πi ξ₀·x}`.
* The Fourier coefficients of a trigonometric polynomial are its coefficients.
* Proposition 1.5.2: Plancherel, Parseval, and `f ↦ f̂` is an isometry `L²(𝕋ⁿ) ≅ ℓ²(ℤⁿ)`.
* Example 3.0.5: `F_{𝕋ⁿ}(P f)(ξ) = (2π|ξ|)^ν f̂(ξ)` for `P = (-Δ)^{ν/2}` (on trigonometric
  polynomials), and more generally `(Op(m) f)^ = m f̂` for any Fourier multiplier.
-/

open Complex MeasureTheory FourierTransform UnitAddTorus Finset
open scoped ComplexConjugate

namespace TorusPsiDO

/-! ### §1.4: the Fourier transform on `ℝ` -/

/-- **Example 1.4.2.** `𝓕(e^{-πx²})(ξ) = e^{-πξ²}`. -/
theorem fourier_gaussian :
    (𝓕 fun x : ℝ => cexp (-Real.pi * x ^ 2)) = fun ξ : ℝ => cexp (-Real.pi * ξ ^ 2) := by
  have := fourier_gaussian_pi (b := 1) (by simp)
  simpa using this

/-- **Proposition 1.4.6 (1).** `|f̂(ξ)| ≤ ‖f‖_{L¹}`. -/
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  Real.norm_fourier_le_integral_norm f ξ

/-- **Theorem 1.4.8 (2), Fourier inversion.** If `f` is continuous and integrable and `f̂` is
integrable, then `(f̂)^∨ = f`. -/
theorem fourier_inversion (f : ℝ → ℂ) (hc : Continuous f) (hf : Integrable f)
    (hf' : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f :=
  hc.fourierInv_fourier_eq hf hf'

/-- **Example 1.4.13.** For the test function `φ(x) = e^{-|x|²}`, the integral
`∫ e^{|x|²} φ(x) dx = ∫ 1 dx` diverges: the function is not integrable. -/
theorem not_integrable_exp_sq_mul_gaussian :
    ¬ Integrable (fun x : ℝ => Real.exp (x ^ 2) * Real.exp (-x ^ 2)) := by
  have h1 : (fun x : ℝ => Real.exp (x ^ 2) * Real.exp (-x ^ 2)) = fun _ => (1 : ℝ) := by
    funext x; rw [← Real.exp_add]; simp
  rw [h1, integrable_const_iff]
  rintro (h | h)
  · norm_num at h
  · have := h.measure_univ_lt_top
    simp at this

/-! ### §1.5: Fourier series on `𝕋ⁿ` -/

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti`, `ℝ/ℤ` carries its normalized Haar measure
(total mass 1); `𝕋ⁿ = (ℝ/ℤ)ⁿ` carries the product measure, i.e. the normalized Lebesgue measure
of §1.5. -/

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {n : ℕ}

/-- `mFourier ξ` evaluated at the class of `x ∈ ℝⁿ` is `e^{2πi x·ξ}`. -/
theorem mFourier_coe (ξ : Fin n → ℤ) (x : Fin n → ℝ) :
    mFourier ξ (fun i => (x i : UnitAddCircle)) = ePow ξ x := by
  simp only [mFourier, ContinuousMap.coe_mk, AddCircle.fourier_coe_apply, ePow, dot]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i _ => by ring

/-- **Example 1.5.4.** `(e^{2πi ξ₀·x})^(ξ) = 1` if `ξ = ξ₀` and `0` otherwise. -/
theorem mFourierCoeff_mFourier (ξ₀ ξ : Fin n → ℤ) :
    mFourierCoeff (mFourier ξ₀ : UnitAddTorus (Fin n) → ℂ) ξ = if ξ = ξ₀ then 1 else 0 := by
  rw [← mFourierCoeff_toLp (mFourier ξ₀) ξ]
  have := mFourierBasis_repr (d := Fin n) (mFourierBasis ξ₀) ξ
  rw [HilbertBasis.repr_self, coe_mFourierBasis] at this
  refine Eq.trans this.symm ?_
  simp [Pi.single_apply]

/-- **Example 1.5.3.** The constant function `1` has `1̂(ξ) = 1` if `ξ = 0` and `0` otherwise. -/
theorem mFourierCoeff_one (ξ : Fin n → ℤ) :
    mFourierCoeff (fun _ : UnitAddTorus (Fin n) => (1 : ℂ)) ξ = if ξ = 0 then 1 else 0 := by
  have h : (fun _ : UnitAddTorus (Fin n) => (1 : ℂ)) =
      (mFourier (0 : Fin n → ℤ) : UnitAddTorus (Fin n) → ℂ) := by
    funext t; simp [mFourier_zero]
  rw [h, mFourierCoeff_mFourier]

/-- The Fourier coefficients of the trigonometric polynomial `∑_{ξ ∈ S} c_ξ e_ξ` are the
`c_ξ`: this justifies writing `f̂ = c` in the definition of `Op` (Definition 2.0.15). -/
theorem mFourierCoeff_trigPoly (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (η : Fin n → ℤ) :
    mFourierCoeff (fun t : UnitAddTorus (Fin n) => ∑ ξ ∈ S, c ξ * mFourier ξ t) η =
      if η ∈ S then c η else 0 := by
  have hint : ∀ ξ, Integrable (fun t : UnitAddTorus (Fin n) =>
      mFourier (-η) t • (c ξ * mFourier ξ t)) := fun ξ =>
    ((mFourier (-η)).continuous.smul
      (continuous_const.mul (mFourier ξ).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : ∀ ξ, ∫ t, mFourier (-η) t • (c ξ * mFourier ξ t) =
      c ξ * (if η = ξ then 1 else 0) := by
    intro ξ
    rw [← mFourierCoeff_mFourier ξ η, mFourierCoeff, ← integral_const_mul]
    congr 1; funext t; simp only [smul_eq_mul]; ring
  rw [mFourierCoeff]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun ξ _ => hint ξ)]
  simp_rw [hterm]
  simp [mul_ite, Finset.sum_ite_eq]

/-- **Proposition 1.5.2 (1), Plancherel.** `‖f‖²_{L²} = ∑_ξ |f̂(ξ)|²`. -/
theorem plancherel (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))) :
    HasSum (fun ξ => ‖mFourierCoeff f ξ‖ ^ 2) (∫ t, ‖f t‖ ^ 2) :=
  hasSum_sq_mFourierCoeff f

/-- **Proposition 1.5.2 (2), Parseval.** `∫ f ḡ = ∑_ξ f̂(ξ) \overline{ĝ(ξ)}`. -/
theorem parseval (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n)))) :
    HasSum (fun ξ => mFourierCoeff f ξ * conj (mFourierCoeff g ξ)) (∫ t, f t * conj (g t)) := by
  have := hasSum_prod_mFourierCoeff g f
  simpa [mul_comm] using this

/-- **Proposition 1.5.2 (3).** `f ↦ (f̂(ξ))_ξ` is a surjective isometry `L²(𝕋ⁿ) → ℓ²(ℤⁿ)`:
the Fourier exponentials form a Hilbert basis (Proposition 1.5.1). -/
theorem fourier_isometry :
    (∀ f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))),
        ‖mFourierBasis.repr f‖ = ‖f‖ ∧ ∀ ξ, mFourierBasis.repr f ξ = mFourierCoeff f ξ) ∧
      Function.Surjective (mFourierBasis (d := Fin n)).repr :=
  ⟨fun f => ⟨LinearIsometryEquiv.norm_map _ f, mFourierBasis_repr f⟩,
    (mFourierBasis (d := Fin n)).repr.surjective⟩

/-- The toroidal quantization of a Fourier multiplier `m`, as a function on `𝕋ⁿ`. -/
noncomputable def OpT (m : (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (t : UnitAddTorus (Fin n)) : ℂ :=
  ∑ ξ ∈ S, mFourier ξ t * m ξ * c ξ

/-- `OpT` is `Op` read on the torus. -/
theorem OpT_coe (m : (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (x : Fin n → ℝ) :
    OpT m S c (fun i => (x i : UnitAddCircle)) = Op (fun _ ξ => m ξ) S c x := by
  simp [OpT, Op, mFourier_coe]

/-- `(Op(m) f)^(ξ) = m(ξ) f̂(ξ)`: `Op(m)` is a Fourier multiplier (Definition 2.0.25). -/
theorem mFourierCoeff_OpT (m : (Fin n → ℤ) → ℂ) (S : Finset (Fin n → ℤ))
    (c : (Fin n → ℤ) → ℂ) (η : Fin n → ℤ) :
    mFourierCoeff (OpT m S c) η = m η *
      mFourierCoeff (fun t : UnitAddTorus (Fin n) => ∑ ξ ∈ S, c ξ * mFourier ξ t) η := by
  have : OpT m S c = fun t => ∑ ξ ∈ S, (m ξ * c ξ) * mFourier ξ t := by
    funext t; simp only [OpT]; refine sum_congr rfl fun ξ _ => by ring
  rw [this, mFourierCoeff_trigPoly, mFourierCoeff_trigPoly]
  split_ifs <;> simp

/-- **Example 3.0.5.** For `P = (-Δ)^{ν/2}` (symbol `(2π|ξ|)^ν`),
`F_{𝕋ⁿ}(P f)(ξ) = (2π|ξ|)^ν f̂(ξ)`. -/
theorem fourier_fracLap (ν : ℝ) (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (η : Fin n → ℤ) :
    mFourierCoeff (OpT (fun ξ => (((2 * Real.pi * normZ ξ) ^ ν : ℝ) : ℂ)) S c) η =
      (((2 * Real.pi * normZ η) ^ ν : ℝ) : ℂ) *
        mFourierCoeff (fun t : UnitAddTorus (Fin n) => ∑ ξ ∈ S, c ξ * mFourier ξ t) η :=
  mFourierCoeff_OpT _ S c η

end TorusPsiDO
