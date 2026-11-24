import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite differences on `ℤⁿ` (Thesis, Chapter 2)

* Definition 2.0.5: forward and backward partial differences `Δ_{ξ_j}`, `Δ̄_{ξ_j}`.
* (2.4)–(2.5): the multi-index differences `Δ^α_ξ`, `Δ̄^α_ξ`.
* Proposition 2.0.7: the explicit formulas (2.6) and (2.7).
* Example 2.0.6: the numerical example `σ(ξ₁, ξ₂) = (ξ₁ + 1)(ξ₂ + 1)`.
* Example 2.0.10 / Remark 2.0.11: differences of `⟨ξ⟩² = 1 + |ξ|²`.

## Implementation

The proof of Proposition 2.0.7 in the thesis writes `Δ_j = E_j - I` with the commuting shift
operators `E_j` and expands `(E - I)^α` with the multivariate binomial theorem.  We follow
exactly this argument, made rigorous as follows: the shifts are the image of the *commutative*
group algebra `ℤ[ℤⁿ]` under the algebra homomorphism `shiftAct` (sending the basis element
`η` to the shift `φ ↦ φ(· + η)`).  We define `Δ^α := shiftAct (∏ⱼ (X_{δⱼ} - 1)^{αⱼ})`; the
binomial expansion is then done in the commutative ring `ℤ[ℤⁿ]`.  The lemma
`fwdMulti_add_single` shows that this is the iterated composition `Δ_{ξ₁}^{α₁} ⋯ Δ_{ξₙ}^{αₙ}`
of the thesis (in any order).
-/

open Finset AddMonoidAlgebra

namespace TorusPsiDO

variable {n : ℕ}

/-- `δ_j ∈ ℤⁿ`, the `j`-th unit vector (Definition 2.0.5). -/
abbrev δ (j : Fin n) : Fin n → ℤ := Pi.single j 1

/-- The order `|α| = α₁ + ⋯ + αₙ` of a multi-index. -/
def absIdx (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- A multi-index seen as a point of `ℤⁿ`. -/
def toZ (β : Fin n → ℕ) : Fin n → ℤ := fun i => (β i : ℤ)

/-- The multi-indices `β ≤ α`. -/
def lowerSet (α : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun j => range (α j + 1)

lemma mem_lowerSet {α β : Fin n → ℕ} : β ∈ lowerSet α ↔ β ≤ α := by
  simp [lowerSet, Fintype.mem_piFinset, Pi.le_def]

section Defs

variable {E : Type*} [AddCommGroup E]

/-- Forward partial difference `Δ_{ξ_j} σ(ξ) = σ(ξ + δ_j) - σ(ξ)` (Definition 2.0.5). -/
def fwd (j : Fin n) (σ : (Fin n → ℤ) → E) : (Fin n → ℤ) → E := fun ξ => σ (ξ + δ j) - σ ξ

/-- Backward partial difference `Δ̄_{ξ_j} σ(ξ) = σ(ξ) - σ(ξ - δ_j)` (Definition 2.0.5). -/
def bwd (j : Fin n) (σ : (Fin n → ℤ) → E) : (Fin n → ℤ) → E := fun ξ => σ ξ - σ (ξ - δ j)

/-- The shift operator `E_η φ = φ(· + η)`. -/
def shift (η : Fin n → ℤ) : Module.End ℤ ((Fin n → ℤ) → E) where
  toFun σ := fun ξ => σ (ξ + η)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `η ↦ E_η` is a monoid homomorphism (the shifts commute). -/
def shiftHom : Multiplicative (Fin n → ℤ) →* Module.End ℤ ((Fin n → ℤ) → E) where
  toFun η := shift (Multiplicative.toAdd η)
  map_one' := by
    apply LinearMap.ext; intro σ; funext ξ
    simp [shift]
  map_mul' a b := by
    apply LinearMap.ext; intro σ; funext ξ
    simp [shift, add_assoc]

/-- The action of the group algebra `ℤ[ℤⁿ]` on functions `ℤⁿ → E` by shifts. -/
noncomputable def shiftAct :
    AddMonoidAlgebra ℤ (Fin n → ℤ) →ₐ[ℤ] Module.End ℤ ((Fin n → ℤ) → E) :=
  AddMonoidAlgebra.lift ℤ (Module.End ℤ ((Fin n → ℤ) → E)) (Fin n → ℤ) shiftHom

lemma shiftAct_single (η : Fin n → ℤ) (r : ℤ) (σ : (Fin n → ℤ) → E) (ξ : Fin n → ℤ) :
    shiftAct (E := E) (single η r) σ ξ = r • σ (ξ + η) := by
  simp [shiftAct, shiftHom, shift]

lemma shiftAct_one (σ : (Fin n → ℤ) → E) : shiftAct (E := E) 1 σ = σ := by
  simp

/-- The polynomial `∏ⱼ (X_{δⱼ} - 1)^{αⱼ}` representing `Δ^α`. -/
noncomputable def fwdPoly (α : Fin n → ℕ) : AddMonoidAlgebra ℤ (Fin n → ℤ) :=
  ∏ j, (single (δ j) 1 - 1) ^ α j

/-- The polynomial `∏ⱼ (1 - X_{-δⱼ})^{αⱼ}` representing `Δ̄^α`. -/
noncomputable def bwdPoly (α : Fin n → ℕ) : AddMonoidAlgebra ℤ (Fin n → ℤ) :=
  ∏ j, (1 - single (-δ j) 1) ^ α j

/-- `Δ^α_ξ` (equation (2.4)). -/
noncomputable def fwdMulti (α : Fin n → ℕ) (σ : (Fin n → ℤ) → E) : (Fin n → ℤ) → E :=
  shiftAct (E := E) (fwdPoly α) σ

/-- `Δ̄^α_ξ` (equation (2.5)). -/
noncomputable def bwdMulti (α : Fin n → ℕ) (σ : (Fin n → ℤ) → E) : (Fin n → ℤ) → E :=
  shiftAct (E := E) (bwdPoly α) σ

lemma fwd_eq_shiftAct (j : Fin n) (σ : (Fin n → ℤ) → E) :
    fwd j σ = shiftAct (E := E) (single (δ j) 1 - 1) σ := by
  funext ξ
  simp [fwd, map_sub, LinearMap.sub_apply, shiftAct_single]

lemma bwd_eq_shiftAct (j : Fin n) (σ : (Fin n → ℤ) → E) :
    bwd j σ = shiftAct (E := E) (1 - single (-δ j) 1) σ := by
  funext ξ
  simp [bwd, map_sub, LinearMap.sub_apply, shiftAct_single, sub_eq_add_neg]

/-- Helper: `∏ᵢ xᵢ ^ (α + δ_j)ᵢ = x_j * ∏ᵢ xᵢ ^ αᵢ` in a commutative monoid. -/
lemma prod_pow_add_single {M : Type*} [CommMonoid M] (x : Fin n → M) (α : Fin n → ℕ)
    (j : Fin n) : ∏ i, x i ^ (α + Pi.single j 1 : Fin n → ℕ) i = x j * ∏ i, x i ^ α i := by
  simp only [Pi.add_apply, pow_add, prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Fintype.prod_eq_single j]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

@[simp] lemma fwdMulti_zero (σ : (Fin n → ℤ) → E) : fwdMulti 0 σ = σ := by
  simp [fwdMulti, fwdPoly]

@[simp] lemma bwdMulti_zero (σ : (Fin n → ℤ) → E) : bwdMulti 0 σ = σ := by
  simp [bwdMulti, bwdPoly]

/-- `Δ^{α + δ_j} = Δ_{ξ_j} ∘ Δ^α`: `Δ^α` is the iterated composition of the partial
differences, in any order (equation (2.4)). -/
lemma fwdMulti_add_single (α : Fin n → ℕ) (j : Fin n) (σ : (Fin n → ℤ) → E) :
    fwdMulti (α + Pi.single j 1) σ = fwd j (fwdMulti α σ) := by
  rw [fwdMulti, fwdPoly, prod_pow_add_single, map_mul, fwd_eq_shiftAct]
  rfl

lemma bwdMulti_add_single (α : Fin n → ℕ) (j : Fin n) (σ : (Fin n → ℤ) → E) :
    bwdMulti (α + Pi.single j 1) σ = bwd j (bwdMulti α σ) := by
  rw [bwdMulti, bwdPoly, prod_pow_add_single, map_mul, bwd_eq_shiftAct]
  rfl

/-- `Δ^{α + β} = Δ^α ∘ Δ^β`. -/
lemma fwdMulti_add (α β : Fin n → ℕ) (σ : (Fin n → ℤ) → E) :
    fwdMulti (α + β) σ = fwdMulti α (fwdMulti β σ) := by
  simp only [fwdMulti, fwdPoly, Pi.add_apply, pow_add, prod_mul_distrib, map_mul]
  rfl

/-- On a single coordinate, `Δ^{k δ_j}` is the `k`-th iterate of `Δ_{ξ_j}`. -/
lemma fwdMulti_single (j : Fin n) (k : ℕ) (σ : (Fin n → ℤ) → E) :
    fwdMulti (Pi.single j k) σ = (fwd j)^[k] σ := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    rw [show (Pi.single j (k + 1) : Fin n → ℕ) = Pi.single j k + Pi.single j 1 by
      rw [← Pi.single_add], fwdMulti_add_single, ih, Function.iterate_succ_apply']

/-- Helper: `∑ⱼ βⱼ • (± δⱼ) = ± β`. -/
lemma sum_smul_delta (β : Fin n → ℕ) : ∑ j, β j • δ j = toZ β := by
  funext i
  simp [toZ, Finset.sum_apply, Pi.single_apply]

/-- Binomial expansion of `(X_v - 1)^k` in `ℤ[ℤⁿ]`. -/
lemma single_sub_one_pow (v : Fin n → ℤ) (k : ℕ) :
    (single v (1 : ℤ) - 1) ^ k =
      ∑ m ∈ range (k + 1), single (m • v) ((-1) ^ (k - m) * (k.choose m : ℤ)) := by
  rw [sub_eq_add_neg, add_pow]
  refine sum_congr rfl fun m _ => ?_
  rw [one_def, ← single_neg, single_pow, single_pow, natCast_def, single_mul_single,
    single_mul_single]
  simp

/-- Binomial expansion of `(1 - X_v)^k` in `ℤ[ℤⁿ]`. -/
lemma one_sub_single_pow (v : Fin n → ℤ) (k : ℕ) :
    (1 - single v (1 : ℤ)) ^ k =
      ∑ m ∈ range (k + 1), single (m • v) ((-1) ^ m * (k.choose m : ℤ)) := by
  rw [sub_eq_neg_add, add_pow]
  refine sum_congr rfl fun m _ => ?_
  rw [one_def, ← single_neg, single_pow, single_pow, natCast_def, single_mul_single,
    single_mul_single]
  simp

/-- The multivariate binomial expansion of `fwdPoly α`. -/
lemma fwdPoly_eq (α : Fin n → ℕ) :
    fwdPoly α = ∑ β ∈ lowerSet α,
      single (toZ β) (∏ j, ((-1) ^ (α j - β j) * ((α j).choose (β j) : ℤ))) := by
  rw [fwdPoly]
  simp_rw [single_sub_one_pow]
  rw [prod_univ_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [prod_single, sum_smul_delta]

lemma bwdPoly_eq (α : Fin n → ℕ) :
    bwdPoly α = ∑ β ∈ lowerSet α,
      single (-toZ β) (∏ j, ((-1) ^ β j * ((α j).choose (β j) : ℤ))) := by
  rw [bwdPoly]
  simp_rw [one_sub_single_pow]
  rw [prod_univ_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [prod_single]
  congr 1
  rw [← sum_smul_delta]
  simp [Finset.sum_neg_distrib]

/-- **Proposition 2.0.7, formula (2.6).**
`Δ^α φ(ξ) = ∑_{β ≤ α} (-1)^{|α-β|} binom(α, β) φ(ξ + β)`, where `(-1)^{|α-β|} binom(α,β)`
is written as `∏ⱼ (-1)^{αⱼ-βⱼ} binom(αⱼ, βⱼ)`. -/
theorem fwdMulti_eq_sum (α : Fin n → ℕ) (φ : (Fin n → ℤ) → E) (ξ : Fin n → ℤ) :
    fwdMulti α φ ξ = ∑ β ∈ lowerSet α,
      (∏ j, ((-1) ^ (α j - β j) * ((α j).choose (β j) : ℤ))) • φ (ξ + toZ β) := by
  rw [fwdMulti, fwdPoly_eq, map_sum, LinearMap.sum_apply, Finset.sum_apply]
  simp [shiftAct_single]

/-- **Proposition 2.0.7, formula (2.7).**
`Δ̄^α φ(ξ) = ∑_{β ≤ α} (-1)^{|β|} binom(α, β) φ(ξ - β)`. -/
theorem bwdMulti_eq_sum (α : Fin n → ℕ) (φ : (Fin n → ℤ) → E) (ξ : Fin n → ℤ) :
    bwdMulti α φ ξ = ∑ β ∈ lowerSet α,
      (∏ j, ((-1) ^ β j * ((α j).choose (β j) : ℤ))) • φ (ξ - toZ β) := by
  rw [bwdMulti, bwdPoly_eq, map_sum, LinearMap.sum_apply, Finset.sum_apply]
  simp [shiftAct_single, sub_eq_add_neg]

/-- The sign in (2.6) is `(-1)^{|α - β|}`. -/
lemma prod_neg_one_pow (α β : Fin n → ℕ) :
    ∏ j, ((-1 : ℤ) ^ (α j - β j)) = (-1) ^ absIdx (α - β) := by
  rw [absIdx, Finset.prod_pow_eq_pow_sum]
  rfl

end Defs

/-! ### Induction on multi-indices -/

lemma sum_single_one (j : Fin n) : ∑ i, (Pi.single j 1 : Fin n → ℕ) i = 1 := by
  simp [Pi.single_apply]

/-- Induction principle: a property of multi-indices that holds for `0` and is preserved
by `α ↦ α + δ_j` holds for every multi-index. -/
theorem multiIndex_induction {P : (Fin n → ℕ) → Prop} (h0 : P 0)
    (hs : ∀ α j, P α → P (α + Pi.single j 1)) : ∀ α, P α := by
  intro α
  induction h : absIdx α generalizing α with
  | zero =>
    have : α = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.mp h) i (mem_univ _)
    subst this; exact h0
  | succ s ih =>
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [absIdx, hc] at h
    have hα : α = (α - Pi.single j 1) + Pi.single j 1 := by
      funext i
      by_cases hi : i = j
      · subst hi; simp; omega
      · simp [Pi.single_apply, hi]
    rw [hα]
    apply hs
    apply ih
    have := congrArg absIdx hα
    simp only [absIdx, Pi.add_apply, sum_add_distrib, sum_single_one] at this
    rw [absIdx] at h
    rw [absIdx]
    omega

lemma absIdx_add_single (α : Fin n → ℕ) (j : Fin n) :
    absIdx (α + Pi.single j 1) = absIdx α + 1 := by
  simp only [absIdx, Pi.add_apply, sum_add_distrib, sum_single_one]

/-! ### Example 2.0.6 -/

section Example206

/-- `σ(ξ₁, ξ₂) = (ξ₁ + 1)(ξ₂ + 1)` on `ℤ²`. -/
def σ₂ (ξ : Fin 2 → ℤ) : ℤ := (ξ 0 + 1) * (ξ 1 + 1)

/-- The table of values of Example 2.0.6. -/
example : σ₂ ![0, 0] = 1 ∧ σ₂ ![0, 1] = 2 ∧ σ₂ ![0, 2] = 3 ∧ σ₂ ![1, 0] = 2 ∧
    σ₂ ![1, 1] = 4 ∧ σ₂ ![1, 2] = 6 ∧ σ₂ ![2, 0] = 3 ∧ σ₂ ![2, 1] = 6 ∧ σ₂ ![2, 2] = 9 := by
  simp [σ₂]

lemma one_add_delta0 : (![1, 1] : Fin 2 → ℤ) + δ 0 = ![2, 1] := by
  funext i; fin_cases i <;> simp [Pi.single_apply]

lemma one_add_delta1 : (![1, 1] : Fin 2 → ℤ) + δ 1 = ![1, 2] := by
  funext i; fin_cases i <;> simp [Pi.single_apply]

/-- `Δ_{ξ₁} σ(1,1) = 2`. -/
theorem ex206_fwd0 : fwd 0 σ₂ ![1, 1] = 2 := by
  simp only [fwd, one_add_delta0]; simp [σ₂]

/-- `Δ_{ξ₂} σ(1,1) = 2`. -/
theorem ex206_fwd1 : fwd 1 σ₂ ![1, 1] = 2 := by
  simp only [fwd, one_add_delta1]; simp [σ₂]

/-- `Δ_{ξ₁} Δ_{ξ₂} σ(1,1) = 9 - 6 - 6 + 4 = 1`. -/
theorem ex206_fwd01 : fwd 0 (fwd 1 σ₂) ![1, 1] = 1 := by
  have h : (![2, 1] : Fin 2 → ℤ) + δ 1 = ![2, 2] := by
    funext i; fin_cases i <;> simp [Pi.single_apply]
  simp only [fwd, one_add_delta0, one_add_delta1, h]; simp [σ₂]

/-- The same value via the multi-index difference `Δ^{(1,1)}`. -/
theorem ex206_multi : fwdMulti ![1, 1] σ₂ ![1, 1] = 1 := by
  have : (![1, 1] : Fin 2 → ℕ) = (0 + Pi.single 1 1) + Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [Pi.single_apply]
  rw [this, fwdMulti_add_single, fwdMulti_add_single, fwdMulti_zero]
  exact ex206_fwd01

end Example206

/-! ### Example 2.0.10 and Remark 2.0.11: differences of `⟨ξ⟩² = 1 + |ξ|²` -/

section Example2010

/-- `a(ξ) = ⟨ξ⟩² = 1 + |ξ|²`, as a complex-valued function on `ℤⁿ`. -/
def bracketSq (ξ : Fin n → ℤ) : ℂ := 1 + ∑ i, ((ξ i : ℂ)) ^ 2

/-- `Δ_{ξ_j} ⟨ξ⟩² = 2 ξ_j + 1` (Example 2.0.10). -/
theorem fwd_bracketSq (j : Fin n) :
    fwd j (bracketSq (n := n)) = fun ξ => 2 * (ξ j : ℂ) + 1 := by
  funext ξ
  simp only [fwd, bracketSq, Pi.add_apply]
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib,
    Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
  simp
  ring

/-- `Δ_{ξ_j} (2 ξ_i + 1) = 2 [i = j]`. -/
theorem fwd_linear (i j : Fin n) :
    fwd j (fun ξ : Fin n → ℤ => 2 * (ξ i : ℂ) + 1) = fun _ => if i = j then 2 else 0 := by
  funext ξ
  by_cases h : i = j
  · subst h; simp [fwd]; ring
  · simp [fwd, Pi.single_apply, h]

theorem fwd_const (j : Fin n) (c : ℂ) : fwd j (fun _ : Fin n → ℤ => c) = fun _ => 0 := by
  funext ξ; simp [fwd]

/-- Remark 2.0.11: `Δ²_{ξ_j} ⟨ξ⟩² = 2`. -/
theorem fwd_fwd_bracketSq (j : Fin n) :
    fwd j (fwd j (bracketSq (n := n))) = fun _ => 2 := by
  rw [fwd_bracketSq, fwd_linear]; simp

/-- Remark 2.0.11: `Δ³_{ξ_j} ⟨ξ⟩² = 0`. -/
theorem fwd_fwd_fwd_bracketSq (j : Fin n) :
    fwd j (fwd j (fwd j (bracketSq (n := n)))) = fun _ => 0 := by
  rw [fwd_fwd_bracketSq, fwd_const]

/-- Complete description of `Δ^α ⟨ξ⟩²` for every multi-index `α`: it is `⟨ξ⟩²` if `|α| = 0`,
some `2ξ_j + 1` if `|α| = 1`, a constant of modulus `≤ 2` if `|α| = 2`, and `0` if `|α| ≥ 3`
(Remarks 2.0.11 and 2.0.12). -/
theorem fwdMulti_bracketSq (α : Fin n → ℕ) :
    (absIdx α = 0 → fwdMulti α (bracketSq (n := n)) = bracketSq) ∧
    (absIdx α = 1 → ∃ j, fwdMulti α (bracketSq (n := n)) = fun ξ => 2 * (ξ j : ℂ) + 1) ∧
    (absIdx α = 2 → ∃ c : ℂ, ‖c‖ ≤ 2 ∧ fwdMulti α (bracketSq (n := n)) = fun _ => c) ∧
    (3 ≤ absIdx α → fwdMulti α (bracketSq (n := n)) = fun _ => 0) := by
  induction α using multiIndex_induction with
  | h0 => exact ⟨fun _ => by simp, fun h => by simp [absIdx] at h,
      fun h => by simp [absIdx] at h, fun h => by simp [absIdx] at h⟩
  | hs α j ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    rw [absIdx_add_single, fwdMulti_add_single]
    rcases (show absIdx α = 0 ∨ absIdx α = 1 ∨ absIdx α = 2 ∨ 3 ≤ absIdx α by omega)
      with h | h | h | h
    · rw [h0 h, fwd_bracketSq]
      exact ⟨fun h' => absurd h' (by omega), fun _ => ⟨j, rfl⟩,
        fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
    · obtain ⟨i, hi⟩ := h1 h
      rw [hi, fwd_linear]
      refine ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
        fun _ => ⟨if i = j then 2 else 0, ?_, rfl⟩, fun h' => absurd h' (by omega)⟩
      split_ifs <;> norm_num
    · obtain ⟨c, -, hc⟩ := h2 h
      rw [hc, fwd_const]
      exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
        fun h' => absurd h' (by omega), fun _ => rfl⟩
    · rw [h3 h, fwd_const]
      exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
        fun h' => absurd h' (by omega), fun _ => rfl⟩

end Example2010

end TorusPsiDO
