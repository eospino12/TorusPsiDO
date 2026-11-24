import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The torus `𝕋ⁿ = ℝⁿ/ℤⁿ` (Thesis, §1.1–§1.2)

* §1.1.1: `φ(θ) = e^{2πiθ}` is a homomorphism `ℝ → 𝕊¹` with kernel `ℤ`, hence `ℝ/ℤ ≅ 𝕊¹`
  (equations (1.2)–(1.5)).
* `𝕋ⁿ = ℝⁿ/ℤⁿ ≅ (ℝ/ℤ)ⁿ` (page 8).
* Theorem 1.2.1: `(A × B)/(C × D) ≅ A/C × B/D`.
* Example 1.2.4: `𝕋ⁿ` is a compact (Hausdorff) topological group.
* Corollary 1.2.2 and equation (1.13): see the section `Correction` below.  Formalizing this
  part showed that the isomorphism `𝕋ⁿ × ℤⁿ ≅ ℝⁿ` claimed in (1.13) and in Remark 1.2.5 is
  **false**, even for abstract groups (`not_nonempty_torus_prod_equiv`): `𝕋ⁿ × ℤⁿ` has an element of
  order 2, `ℝⁿ` has none.  The proof in the thesis quotients `ℝⁿ × ℤⁿ` by two *different*
  copies of `ℤⁿ` (`ℤⁿ × {0}` in Corollary 1.2.2, `{0} × ℤⁿ = ker φ` in (1.10)–(1.11)); both
  correct statements are proved here.
-/

open Complex

namespace TorusPsiDO

/-! ### §1.1.1  The isomorphism `ℝ/ℤ ≅ 𝕊¹` -/

/-- `φ(θ) = e^{2πiθ}`, as a homomorphism from `(ℝ, +)` to the (additively written) circle. -/
noncomputable def expHom : ℝ →+ Additive Circle where
  toFun θ := Additive.ofMul (Circle.exp (2 * Real.pi * θ))
  map_zero' := by simp
  map_add' a b := by
    rw [mul_add, Circle.exp_add]
    rfl

lemma expHom_apply_coe (θ : ℝ) :
    ((Additive.toMul (expHom θ) : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * θ) := by
  simp only [expHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Circle.coe_exp]
  push_cast
  ring_nf

/-- Equations (1.2)–(1.4): `e^{2πiθ} = 1 ⟺ θ ∈ ℤ`. -/
theorem exp_two_pi_I_eq_one_iff (θ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * θ) = 1 ↔ ∃ k : ℤ, (k : ℝ) = θ := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (θ : ℂ) = k := by
      have := hk
      apply mul_left_cancel₀ hpi
      rw [this]; ring
    exact_mod_cast this.symm
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- The kernel of `φ` is `ℤ` (equation (1.5)). -/
theorem ker_expHom : expHom.ker = AddSubgroup.zmultiples (1 : ℝ) := by
  ext θ
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
  have h : expHom θ = 0 ↔ Complex.exp (2 * Real.pi * Complex.I * θ) = 1 := by
    rw [← expHom_apply_coe]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [h]; rfl
  rw [h, exp_two_pi_I_eq_one_iff]
  simp [zsmul_eq_mul]

lemma expHom_surjective : Function.Surjective expHom := by
  intro z
  obtain ⟨t, ht⟩ := Circle.exp_surjective (Additive.toMul z)
  refine ⟨t / (2 * Real.pi), ?_⟩
  apply Additive.toMul.injective
  simp only [expHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul]
  rw [← ht]
  congr 1
  field_simp

/-- **§1.1.1 (equation (1.5)).** `ℝ/ℤ ≅ 𝕊¹` as groups, via the first isomorphism theorem
applied to `φ(θ) = e^{2πiθ}`. -/
noncomputable def addCircleEquivCircle : AddCircle (1 : ℝ) ≃+ Additive Circle :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_expHom.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective expHom expHom_surjective)

/-! ### `𝕋ⁿ = ℝⁿ/ℤⁿ` -/

variable {n : ℕ}

/-- The lattice `ℤⁿ ⊂ ℝⁿ`. -/
def intLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) where
  carrier := {x | ∀ i, ∃ k : ℤ, (k : ℝ) = x i}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb i
    obtain ⟨p, hp⟩ := ha i
    obtain ⟨q, hq⟩ := hb i
    exact ⟨p + q, by simp [hp, hq]⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨p, hp⟩ := ha i
    exact ⟨-p, by simp [hp]⟩

lemma mem_intLattice {x : Fin n → ℝ} : x ∈ intLattice n ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = x i :=
  Iff.rfl

/-- The `n`-dimensional torus `𝕋ⁿ = ℝⁿ/ℤⁿ`. -/
abbrev Torus (n : ℕ) := (Fin n → ℝ) ⧸ intLattice n

/-- The coordinatewise projection `ℝⁿ → (ℝ/ℤ)ⁿ`. -/
def coordProj (n : ℕ) : (Fin n → ℝ) →+ (Fin n → AddCircle (1 : ℝ)) :=
  AddMonoidHom.compLeft (QuotientAddGroup.mk' _) (Fin n)

lemma ker_coordProj : (coordProj n).ker = intLattice n := by
  ext x
  simp only [AddMonoidHom.mem_ker, coordProj, mem_intLattice]
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  simp only [AddMonoidHom.compLeft_apply, Function.comp_apply, QuotientAddGroup.mk'_apply,
    Pi.zero_apply, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]

lemma coordProj_surjective : Function.Surjective (coordProj n) := by
  intro y
  choose x hx using fun i => QuotientAddGroup.mk_surjective (y i)
  exact ⟨x, funext hx⟩

/-- **Page 8.** `𝕋ⁿ = ℝⁿ/ℤⁿ ≅ (ℝ/ℤ) × ⋯ × (ℝ/ℤ)`. -/
noncomputable def torusEquivPi : Torus n ≃+ (Fin n → AddCircle (1 : ℝ)) :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_coordProj.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ coordProj_surjective)

/-- **Example 1.2.4.** `𝕋ⁿ ≅ (ℝ/ℤ)ⁿ` is a compact Hausdorff topological group. -/
example : IsTopologicalAddGroup (Fin n → AddCircle (1 : ℝ)) ∧
    CompactSpace (Fin n → AddCircle (1 : ℝ)) ∧ T2Space (Fin n → AddCircle (1 : ℝ)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### Theorem 1.2.1 -/

/-- **Theorem 1.2.1.** If `C ◁ A` and `D ◁ B`, then `(A × B)/(C × D) ≅ (A/C) × (B/D)`. -/
noncomputable def quotientProdEquiv {A B : Type*} [AddGroup A] [AddGroup B]
    (C : AddSubgroup A) (D : AddSubgroup B) [C.Normal] [D.Normal] :
    (A × B) ⧸ C.prod D ≃+ (A ⧸ C) × (B ⧸ D) :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      rw [AddMonoidHom.ker_prodMap, QuotientAddGroup.ker_mk', QuotientAddGroup.ker_mk'])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      ((QuotientAddGroup.mk' C).prodMap (QuotientAddGroup.mk' D)) (by
        rintro ⟨x, y⟩
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
        exact ⟨(a, b), rfl⟩))

/-! ### Correction of Corollary 1.2.2 and of equation (1.13) -/

section Correction

/-- **Corollary 1.2.2 (correct form).** Quotienting by `ℤⁿ × {0}`:
`(ℝⁿ × ℤⁿ)/(ℤⁿ × {0}) ≅ 𝕋ⁿ × ℤⁿ`. -/
noncomputable def quotient_lattice_prod_bot :
    ((Fin n → ℝ) × (Fin n → ℤ)) ⧸ (intLattice n).prod ⊥ ≃+ Torus n × (Fin n → ℤ) :=
  (quotientProdEquiv _ _).trans
    (AddEquiv.prodCongr (AddEquiv.refl _) (QuotientAddGroup.quotientBot))

/-- **Equations (1.10)–(1.11) (correct form).** With `φ(a, b) = a`, `ker φ = {0} × ℤⁿ` and
`(ℝⁿ × ℤⁿ)/({0} × ℤⁿ) ≅ ℝⁿ`. -/
noncomputable def quotient_bot_prod_top :
    ((Fin n → ℝ) × (Fin n → ℤ)) ⧸ (⊥ : AddSubgroup (Fin n → ℝ)).prod ⊤ ≃+ (Fin n → ℝ) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (AddMonoidHom.ker_fst (G := Fin n → ℝ) (G' := Fin n → ℤ)).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (AddMonoidHom.fst (Fin n → ℝ) (Fin n → ℤ))
      Prod.fst_surjective)

/-- The point `(1/2, …, 1/2) + ℤⁿ` of `𝕋ⁿ`. -/
noncomputable def halfPoint (n : ℕ) : Torus n := QuotientAddGroup.mk (fun _ => (1 / 2 : ℝ))

lemma two_nsmul_halfPoint : (2 : ℕ) • halfPoint n = 0 := by
  rw [halfPoint, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  intro i
  exact ⟨1, by simp⟩

lemma halfPoint_ne_zero (hn : 0 < n) : halfPoint n ≠ 0 := by
  rw [halfPoint, Ne, QuotientAddGroup.eq_zero_iff]
  intro h
  obtain ⟨k, hk⟩ := h ⟨0, hn⟩
  have h2 : ((2 * k : ℤ) : ℝ) = 1 := by push_cast; rw [hk]; norm_num
  have : 2 * k = 1 := by exact_mod_cast h2
  omega

/-- **Equation (1.13) and Remark 1.2.5 are false.** For `n ≥ 1` there is **no** group
isomorphism `𝕋ⁿ × ℤⁿ ≅ ℝⁿ`, not even ignoring the topology: the element
`((1/2, …, 1/2) + ℤⁿ, 0)` has order 2, while `ℝⁿ` is torsion-free. -/
theorem not_nonempty_torus_prod_equiv (hn : 0 < n) :
    IsEmpty (Torus n × (Fin n → ℤ) ≃+ (Fin n → ℝ)) := by
  refine ⟨fun e => ?_⟩
  set t : Torus n × (Fin n → ℤ) := (halfPoint n, 0)
  have ht : t ≠ 0 := by
    intro h
    exact halfPoint_ne_zero hn (congrArg Prod.fst h)
  have h2 : (2 : ℕ) • t = 0 := by
    simp only [t, Prod.smul_mk, two_nsmul_halfPoint, smul_zero, Prod.mk_zero_zero]
  have he : e t = 0 := by
    have h2' : (2 : ℕ) • e t = 0 := by rw [← map_nsmul, h2, map_zero]
    funext i
    have := congrFun h2' i
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply] at this
    simpa using this
  exact ht (e.injective (he.trans (map_zero e).symm))

end Correction

end TorusPsiDO
