import TorusPsiDO.Differences
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Toroidal symbol classes `S^m_{ρ,δ}(𝕋ⁿ × ℤⁿ)` (Thesis, Chapter 2)

* The discrete Japanese bracket `⟨ξ⟩ = (1 + |ξ|²)^{1/2}` (before Definition 2.0.9).
* Definition 2.0.9: the class `S^m_{ρ,δ}(𝕋ⁿ × ℤⁿ)`.
* Example 2.0.10: `a(x, ξ) = ⟨ξ⟩² ∈ S²_{1,0}(𝕋ⁿ × ℤⁿ)`.
* Basic structure: the classes are increasing in `m`, and closed under addition.

## Conventions

Following Definition 1.3.1 of the thesis, a function on `𝕋ⁿ` is a `1`-periodic function on
`ℝⁿ`.  A symbol is therefore a function `a : ℝⁿ → ℤⁿ → ℂ`, `1`-periodic and smooth in `x`.
The `x`-derivatives `∂^β_x` of order `|β| = k` are encoded by the `k`-th Fréchet derivative
`iteratedFDeriv ℝ k`; its operator norm is equivalent (up to constants depending only on `n`
and `k`) to `max_{|β| = k} |∂^β_x a|`, so the class defined here is the class of the thesis.
-/

open Finset

namespace TorusPsiDO

variable {n : ℕ}

/-- The Euclidean norm `|ξ| = (ξ₁² + ⋯ + ξₙ²)^{1/2}` of `ξ ∈ ℤⁿ`. -/
noncomputable def normZ (ξ : Fin n → ℤ) : ℝ := Real.sqrt (∑ i, ((ξ i : ℝ)) ^ 2)

/-- The discrete Japanese bracket `⟨ξ⟩ = (1 + |ξ|²)^{1/2}`. -/
noncomputable def jbr (ξ : Fin n → ℤ) : ℝ := Real.sqrt (1 + ∑ i, ((ξ i : ℝ)) ^ 2)

lemma sum_sq_nonneg (ξ : Fin n → ℤ) : 0 ≤ ∑ i, ((ξ i : ℝ)) ^ 2 :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma jbr_sq (ξ : Fin n → ℤ) : jbr ξ ^ 2 = 1 + ∑ i, ((ξ i : ℝ)) ^ 2 :=
  Real.sq_sqrt (by linarith [sum_sq_nonneg ξ])

lemma normZ_sq (ξ : Fin n → ℤ) : normZ ξ ^ 2 = ∑ i, ((ξ i : ℝ)) ^ 2 :=
  Real.sq_sqrt (sum_sq_nonneg ξ)

lemma jbr_sq_eq (ξ : Fin n → ℤ) : jbr ξ ^ 2 = 1 + normZ ξ ^ 2 := by
  rw [jbr_sq, normZ_sq]

lemma one_le_jbr (ξ : Fin n → ℤ) : 1 ≤ jbr ξ := by
  rw [jbr, Real.le_sqrt zero_le_one] <;> nlinarith [sum_sq_nonneg ξ]

lemma jbr_pos (ξ : Fin n → ℤ) : 0 < jbr ξ := lt_of_lt_of_le zero_lt_one (one_le_jbr ξ)

lemma normZ_nonneg (ξ : Fin n → ℤ) : 0 ≤ normZ ξ := Real.sqrt_nonneg _

lemma normZ_le_jbr (ξ : Fin n → ℤ) : normZ ξ ≤ jbr ξ :=
  Real.sqrt_le_sqrt (by linarith)

/-- `|ξ_j| ≤ |ξ| ≤ ⟨ξ⟩`. -/
lemma abs_coord_le_normZ (ξ : Fin n → ℤ) (j : Fin n) : |(ξ j : ℝ)| ≤ normZ ξ := by
  rw [normZ, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (single_le_sum (f := fun i => ((ξ i : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j))

lemma abs_coord_le_jbr (ξ : Fin n → ℤ) (j : Fin n) : |(ξ j : ℝ)| ≤ jbr ξ :=
  (abs_coord_le_normZ ξ j).trans (normZ_le_jbr ξ)

/-- For `|ξ| ≥ 1`: `⟨ξ⟩ ≤ √2 |ξ| ≤ 2|ξ|`. -/
lemma jbr_le_two_normZ {ξ : Fin n → ℤ} (h : 1 ≤ normZ ξ) : jbr ξ ≤ 2 * normZ ξ := by
  have h1 := jbr_sq_eq ξ
  nlinarith [jbr_pos ξ, normZ_nonneg ξ]

/-- `⟨ξ⟩^s` is monotone in `s`, because `⟨ξ⟩ ≥ 1`. -/
lemma jbr_rpow_le_rpow (ξ : Fin n → ℤ) {s t : ℝ} (h : s ≤ t) : jbr ξ ^ s ≤ jbr ξ ^ t :=
  Real.rpow_le_rpow_of_exponent_le (one_le_jbr ξ) h

/-- The toroidal differences in `ξ` of a symbol, for fixed `x`: `Δ^α_ξ a(x, ξ)`. -/
noncomputable def diffξ (α : Fin n → ℕ) (a : (Fin n → ℝ) → (Fin n → ℤ) → ℂ) :
    (Fin n → ℝ) → (Fin n → ℤ) → ℂ :=
  fun x => fwdMulti α (a x)

/-- `ℤⁿ ⊂ ℝⁿ`. -/
def toR (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)

/-- **Definition 2.0.9.** The toroidal symbol class `S^m_{ρ,δ}(𝕋ⁿ × ℤⁿ)`: functions
`a(x, ξ)`, `1`-periodic and smooth in `x`, with
`|Δ^α_ξ ∂^β_x a(x, ξ)| ≤ C_{α,β} ⟨ξ⟩^{m - ρ|α| + δ|β|}`. -/
def SymbolClass (n : ℕ) (m ρ δ : ℝ) : Set ((Fin n → ℝ) → (Fin n → ℤ) → ℂ) :=
  {a | (∀ ξ, ContDiff ℝ (⊤ : ℕ∞) fun x => a x ξ) ∧
       (∀ x ξ (k : Fin n → ℤ), a (x + toR k) ξ = a x ξ) ∧
       ∀ (α : Fin n → ℕ) (k : ℕ), ∃ C : ℝ, ∀ x ξ,
         ‖iteratedFDeriv ℝ k (fun x => diffξ α a x ξ) x‖ ≤
           C * jbr ξ ^ (m - ρ * (absIdx α : ℝ) + δ * (k : ℝ))}

/-- The classes increase with the order: `S^m_{ρ,δ} ⊆ S^{m'}_{ρ,δ}` for `m ≤ m'`. -/
theorem SymbolClass.mono {m m' ρ δ : ℝ} (h : m ≤ m') :
    SymbolClass n m ρ δ ⊆ SymbolClass n m' ρ δ := by
  rintro a ⟨hs, hp, hb⟩
  refine ⟨hs, hp, fun α k => ?_⟩
  obtain ⟨C, hC⟩ := hb α k
  refine ⟨max C 0, fun x ξ => (hC x ξ).trans ?_⟩
  calc C * jbr ξ ^ (m - ρ * (absIdx α : ℝ) + δ * k)
      ≤ max C 0 * jbr ξ ^ (m - ρ * (absIdx α : ℝ) + δ * k) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (jbr_pos ξ).le _)
    _ ≤ max C 0 * jbr ξ ^ (m' - ρ * (absIdx α : ℝ) + δ * k) := by
        exact mul_le_mul_of_nonneg_left (jbr_rpow_le_rpow ξ (by linarith)) (le_max_right _ _)

/-! ### Example 2.0.10: `⟨ξ⟩² ∈ S²_{1,0}` -/

lemma norm_bracketSq (ξ : Fin n → ℤ) : ‖bracketSq ξ‖ = jbr ξ ^ 2 := by
  have : bracketSq ξ = ((1 + ∑ i, ((ξ i : ℝ)) ^ 2 : ℝ) : ℂ) := by
    simp [bracketSq]
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith [sum_sq_nonneg ξ]), jbr_sq]

/-- The estimate `|Δ^α ⟨ξ⟩²| ≤ 3 ⟨ξ⟩^{2 - |α|}` behind Example 2.0.10. -/
theorem norm_fwdMulti_bracketSq_le (α : Fin n → ℕ) (ξ : Fin n → ℤ) :
    ‖fwdMulti α (bracketSq (n := n)) ξ‖ ≤ 3 * jbr ξ ^ (2 - (absIdx α : ℝ)) := by
  obtain ⟨h0, h1, h2, h3⟩ := fwdMulti_bracketSq (n := n) α
  have hj := one_le_jbr ξ
  rcases (show absIdx α = 0 ∨ absIdx α = 1 ∨ absIdx α = 2 ∨ 3 ≤ absIdx α by omega)
    with h | h | h | h
  · rw [h0 h, norm_bracketSq, h]
    norm_num
    nlinarith
  · obtain ⟨j, hj'⟩ := h1 h
    rw [hj', h]
    norm_num
    calc ‖2 * (ξ j : ℂ) + 1‖ ≤ ‖2 * (ξ j : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 * |(ξ j : ℝ)| + 1 := by simp
      _ ≤ 2 * jbr ξ + 1 := by linarith [abs_coord_le_jbr ξ j]
      _ ≤ 3 * jbr ξ := by linarith
  · obtain ⟨c, hc, hc'⟩ := h2 h
    rw [hc', h]
    norm_num
    linarith
  · rw [h3 h]
    simp only [norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (jbr_pos ξ).le _)

/-- **Example 2.0.10.** `a(x, ξ) = ⟨ξ⟩² = 1 + |ξ|²` belongs to `S²_{1,0}(𝕋ⁿ × ℤⁿ)`. -/
theorem bracketSq_mem_S2 : (fun (_ : Fin n → ℝ) ξ => bracketSq ξ) ∈ SymbolClass n 2 1 0 := by
  refine ⟨fun ξ => contDiff_const, fun _ _ _ => rfl, fun α k => ⟨3, fun x ξ => ?_⟩⟩
  simp only [diffξ, one_mul, zero_mul, add_zero]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [norm_iteratedFDeriv_zero]
    exact norm_fwdMulti_bracketSq_le α ξ
  · rw [iteratedFDeriv_const_of_ne hk.ne', Pi.zero_apply, norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (jbr_pos ξ).le _)

end TorusPsiDO
