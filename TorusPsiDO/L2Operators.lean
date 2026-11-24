import TorusPsiDO.Symbols
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Bounded operators on `ℓ²(ℤⁿ)`

Auxiliary file for the Fredholm part of Theorem 3.0.4.

* `diagL2 d`: the diagonal (Fourier multiplier) operator `v ↦ (d(ξ) v(ξ))_ξ`, for bounded `d`.
* `kerL2 m`: the operator `v ↦ (∑_η m(ξ, η) v(η))_ξ` defined by a kernel with
  `|m(ξ, η)| ≤ g(ξ - η)`, `g ∈ ℓ¹(ℤⁿ)`.  Its boundedness on `ℓ²` (a Schur / Young
  inequality, `schur_bound`) is proved here from scratch.
-/

open Finset

namespace TorusPsiDO

variable {n : ℕ}

/-- `ℓ²(ℤⁿ)`. -/
noncomputable abbrev L2 (n : ℕ) := lp (fun _ : Fin n → ℤ => ℂ) 2

lemma memℓp_two_iff {f : (Fin n → ℤ) → ℂ} : Memℓp f 2 ↔ Summable fun i => ‖f i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

lemma L2.summable_sq (v : L2 n) : Summable fun i => ‖v i‖ ^ 2 := memℓp_two_iff.mp v.2

lemma L2.norm_sq (v : L2 n) : ‖v‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  simpa using this

/-- Build a bounded operator on `ℓ²` from a linear operation on sequences with an `ℓ²` bound. -/
noncomputable def mkL2 (T : ((Fin n → ℤ) → ℂ) → ((Fin n → ℤ) → ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hadd : ∀ u v : L2 n, T ⇑(u + v) = T ⇑u + T ⇑v)
    (hsmul : ∀ (c : ℂ) (u : L2 n), T ⇑(c • u) = c • T ⇑u)
    (hbd : ∀ v : L2 n, Summable (fun i => ‖T v i‖ ^ 2) ∧ ∑' i, ‖T v i‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2) :
    L2 n →L[ℂ] L2 n :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨T v, memℓp_two_iff.mpr (hbd v).1⟩
      map_add' := fun u v => lp.ext (by
        change T ⇑(u + v) = fun ξ => T u ξ + T v ξ
        funext ξ; exact congrFun (hadd u v) ξ)
      map_smul' := fun c u => lp.ext (by
        change T ⇑(c • u) = fun ξ => c * T u ξ
        funext ξ; exact congrFun (hsmul c u) ξ) }
    C (fun v => by
      have h1 : ‖(⟨T v, memℓp_two_iff.mpr (hbd v).1⟩ : L2 n)‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
        rw [L2.norm_sq, mul_pow]
        exact (hbd v).2
      have h2 : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg _)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) h2 two_ne_zero).mp h1)

lemma le_of_sq_le_sq'_aux : True := trivial

@[simp] lemma mkL2_apply (T : ((Fin n → ℤ) → ℂ) → ((Fin n → ℤ) → ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hadd) (hsmul) (hbd) (v : L2 n) (ξ : Fin n → ℤ) :
    mkL2 T C hC hadd hsmul hbd v ξ = T v ξ := rfl

lemma norm_mkL2_le (T : ((Fin n → ℤ) → ℂ) → ((Fin n → ℤ) → ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hadd) (hsmul) (hbd) : ‖mkL2 (n := n) T C hC hadd hsmul hbd‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-! ### Diagonal operators -/

/-- The diagonal operator `v ↦ (d(ξ) v(ξ))_ξ`, for `|d| ≤ C`. -/
noncomputable def diagL2 (d : (Fin n → ℤ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ ξ, ‖d ξ‖ ≤ C) :
    L2 n →L[ℂ] L2 n :=
  mkL2 (fun v ξ => d ξ * v ξ) C hC
    (fun u v => by funext ξ; simp [lp.coeFn_add, mul_add])
    (fun c u => by funext ξ; simp [lp.coeFn_smul]; ring)
    (fun v => by
      have hle : ∀ i, ‖d i * v i‖ ^ 2 ≤ C ^ 2 * ‖v i‖ ^ 2 := fun i => by
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd i) 2)
          (sq_nonneg _)
      have hs : Summable fun i => C ^ 2 * ‖v i‖ ^ 2 := (L2.summable_sq v).mul_left _
      refine ⟨Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hs, ?_⟩
      rw [L2.norm_sq, ← tsum_mul_left]
      exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hs) hs)

@[simp] lemma diagL2_apply (d : (Fin n → ℤ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ ξ, ‖d ξ‖ ≤ C)
    (v : L2 n) (ξ : Fin n → ℤ) : diagL2 d C hC hd v ξ = d ξ * v ξ := rfl

lemma norm_diagL2_le (d : (Fin n → ℤ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hd : ∀ ξ, ‖d ξ‖ ≤ C) :
    ‖diagL2 d C hC hd‖ ≤ C :=
  norm_mkL2_le _ _ _ _ _ _

/-! ### Kernel operators: the Schur bound -/

section Schur

variable (g : (Fin n → ℤ) → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g)
variable (m : (Fin n → ℤ) → (Fin n → ℤ) → ℂ) (hm : ∀ ξ η, ‖m ξ η‖ ≤ g (ξ - η))

include hg in
lemma summable_shift (ξ : Fin n → ℤ) : Summable fun η => g (ξ - η) :=
  (Equiv.subLeft ξ).summable_iff.mpr hg

lemma tsum_shift (ξ : Fin n → ℤ) : ∑' η, g (ξ - η) = ∑' k, g k :=
  Equiv.tsum_eq (Equiv.subLeft ξ) g

include hg in
lemma summable_shift' (η : Fin n → ℤ) : Summable fun ξ => g (ξ - η) :=
  (Equiv.subRight η).summable_iff.mpr hg

lemma tsum_shift' (η : Fin n → ℤ) : ∑' ξ, g (ξ - η) = ∑' k, g k :=
  Equiv.tsum_eq (Equiv.subRight η) g

include hg0 hg hm in
/-- **Schur / Young inequality on `ℤⁿ`.** If `|m(ξ, η)| ≤ g(ξ - η)` with `g ≥ 0` summable,
then `v ↦ ∑_η m(·, η) v(η)` maps `ℓ²` to `ℓ²`, with norm `≤ ∑ g + 1`. -/
theorem schur_bound (f : (Fin n → ℤ) → ℂ) (hf : Summable fun i => ‖f i‖ ^ 2) :
    (∀ ξ, Summable fun η => m ξ η * f η) ∧
    Summable (fun ξ => ‖∑' η, m ξ η * f η‖ ^ 2) ∧
    ∑' ξ, ‖∑' η, m ξ η * f η‖ ^ 2 ≤ (∑' k, g k + 1) ^ 2 * ∑' i, ‖f i‖ ^ 2 := by
  set G := ∑' k, g k with hGdef
  set c := G + 1 with hcdef
  have hG0 : 0 ≤ G := tsum_nonneg hg0
  have hc : 0 < c := by linarith
  have hgle : ∀ k, g k ≤ G := fun k => hg.le_tsum k (fun j _ => hg0 j)
  set a : (Fin n → ℤ) → ℝ := fun η => ‖f η‖ with ha
  have ha0 : ∀ η, 0 ≤ a η := fun η => norm_nonneg _
  have hsum2 : ∀ ξ, Summable fun η => g (ξ - η) * a η ^ 2 := fun ξ =>
    Summable.of_nonneg_of_le (fun η => mul_nonneg (hg0 _) (sq_nonneg _))
      (fun η => mul_le_mul_of_nonneg_right (hgle _) (sq_nonneg _)) (hf.mul_left G)
  have hsum3 : ∀ ξ, Summable fun η => g (ξ - η) * a η := fun ξ =>
    Summable.of_nonneg_of_le (fun η => mul_nonneg (hg0 _) (ha0 _))
      (fun η => by
        have h1 := hgle (ξ - η)
        have h2 := hg0 (ξ - η)
        have h3 := ha0 η
        show g (ξ - η) * a η ≤ (G * g (ξ - η) + a η ^ 2) / 2
        nlinarith [sq_nonneg (g (ξ - η) - a η)])
      ((((summable_shift g hg ξ).mul_left G).add hf).div_const 2)
  have hsum4 : ∀ ξ, Summable fun η => ‖m ξ η * f η‖ := fun ξ =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun η => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hm ξ η) (norm_nonneg _)) (hsum3 ξ)
  -- pointwise bound
  have hpt : ∀ ξ, ‖∑' η, m ξ η * f η‖ ^ 2 ≤ c * ∑' η, g (ξ - η) * a η ^ 2 := by
    intro ξ
    set S := ∑' η, g (ξ - η) * a η
    set W := ∑' η, g (ξ - η) * a η ^ 2
    have hS : ‖∑' η, m ξ η * f η‖ ≤ S :=
      (norm_tsum_le_tsum_norm (hsum4 ξ)).trans
        (Summable.tsum_le_tsum (fun η => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm ξ η) (norm_nonneg _))
          (hsum4 ξ) (hsum3 ξ))
    have hS0 : 0 ≤ S := tsum_nonneg fun η => mul_nonneg (hg0 _) (ha0 _)
    have hquad : ∀ t : ℝ, 2 * t * S ≤ t ^ 2 * c + W := by
      intro t
      have h1 : 2 * t * S = ∑' η, 2 * t * (g (ξ - η) * a η) := (tsum_mul_left).symm
      have h2 : ∑' η, (t ^ 2 * g (ξ - η) + g (ξ - η) * a η ^ 2) = t ^ 2 * G + W := by
        rw [Summable.tsum_add ((summable_shift g hg ξ).mul_left _) (hsum2 ξ), tsum_mul_left,
          tsum_shift]
      have h3 : ∑' η, 2 * t * (g (ξ - η) * a η) ≤
          ∑' η, (t ^ 2 * g (ξ - η) + g (ξ - η) * a η ^ 2) :=
        Summable.tsum_le_tsum (fun η => by
            have h := mul_nonneg (hg0 (ξ - η)) (sq_nonneg (t - a η))
            have e : g (ξ - η) * (t - a η) ^ 2 =
                t ^ 2 * g (ξ - η) + g (ξ - η) * a η ^ 2 - 2 * t * (g (ξ - η) * a η) := by ring
            linarith)
          ((hsum3 ξ).mul_left _)
          (((summable_shift g hg ξ).mul_left _).add (hsum2 ξ))
      have e : t ^ 2 * c = t ^ 2 * G + t ^ 2 := by rw [hcdef]; ring
      nlinarith [sq_nonneg t]
    have hSW : S ^ 2 ≤ c * W := by
      have := hquad (S / c)
      have e1 : 2 * (S / c) * S = 2 * (S ^ 2 / c) := by ring
      have e2 : (S / c) ^ 2 * c = S ^ 2 / c := by field_simp
      rw [e1, e2] at this
      have : S ^ 2 / c ≤ W := by linarith
      rw [div_le_iff₀ hc] at this
      linarith
    calc ‖∑' η, m ξ η * f η‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
      _ ≤ c * W := hSW
  -- finite partial sums
  have hpartial : ∀ u : Finset (Fin n → ℤ),
      ∑ ξ ∈ u, ‖∑' η, m ξ η * f η‖ ^ 2 ≤ c ^ 2 * ∑' i, ‖f i‖ ^ 2 := by
    intro u
    have hF0 : 0 ≤ ∑' i, ‖f i‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    calc ∑ ξ ∈ u, ‖∑' η, m ξ η * f η‖ ^ 2
        ≤ ∑ ξ ∈ u, c * ∑' η, g (ξ - η) * a η ^ 2 := sum_le_sum fun ξ _ => hpt ξ
      _ = c * ∑' η, ∑ ξ ∈ u, g (ξ - η) * a η ^ 2 := by
          rw [← mul_sum, Summable.tsum_finsetSum (fun ξ _ => hsum2 ξ)]
      _ ≤ c * ∑' η, G * a η ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun η => ?_)
            (summable_sum fun ξ _ => hsum2 ξ) (hf.mul_left G)) hc.le
          rw [← sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          calc ∑ ξ ∈ u, g (ξ - η) ≤ ∑' ξ, g (ξ - η) :=
                (summable_shift' g hg η).sum_le_tsum u (fun j _ => hg0 _)
            _ = G := tsum_shift' g η
      _ = c * (G * ∑' i, ‖f i‖ ^ 2) := by rw [tsum_mul_left]
      _ ≤ c ^ 2 * ∑' i, ‖f i‖ ^ 2 := by
          rw [sq, mul_assoc]
          gcongr
          linarith
  refine ⟨fun ξ => (hsum4 ξ).of_norm, summable_of_sum_le (fun _ => sq_nonneg _) hpartial,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hpartial⟩

/-- The kernel operator `v ↦ (∑_η m(ξ, η) v(η))_ξ` on `ℓ²(ℤⁿ)`. -/
noncomputable def kerL2 : L2 n →L[ℂ] L2 n :=
  mkL2 (fun v ξ => ∑' η, m ξ η * v η) (∑' k, g k + 1)
    (add_nonneg (tsum_nonneg hg0) zero_le_one)
    (fun u v => by
      funext ξ
      have hu := (schur_bound g hg0 hg m hm u (L2.summable_sq u)).1 ξ
      have hv := (schur_bound g hg0 hg m hm v (L2.summable_sq v)).1 ξ
      simp only [lp.coeFn_add, Pi.add_apply, mul_add]
      exact Summable.tsum_add hu hv)
    (fun c u => by
      funext ξ
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← tsum_mul_left]
      congr 1; funext η; ring)
    (fun v => by rw [L2.norm_sq]; exact (schur_bound g hg0 hg m hm v (L2.summable_sq v)).2)

lemma kerL2_apply (v : L2 n) (ξ : Fin n → ℤ) :
    kerL2 g hg0 hg m hm v ξ = ∑' η, m ξ η * v η := rfl

end Schur

end TorusPsiDO
