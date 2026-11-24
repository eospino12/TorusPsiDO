# TorusPsiDO — formalización en Lean 4 de *Sobre los Operadores Pseudodiferenciales en el Toro*

Formalización en **Lean 4 + Mathlib** de la tesis de pregrado

> Esteban Daniel Ospino Tafur, *Sobre los Operadores Pseudodiferenciales en el Toro*,
> Universidad del Valle, 2025. Director: Ph.D. Julio César Delgado Valencia.

**Estado:** `lake build` termina **sin errores y sin `sorry`**. Los 41 resultados principales,
verificados con `#print axioms`, usan solo los axiomas estándar (`propext`, `Classical.choice`,
`Quot.sound`). Incluye la **propiedad de Fredholm del Teorema 3.0.4**.

*English summary:* a Lean 4 / Mathlib formalization of an undergraduate thesis on periodic
pseudo-differential operators on the torus 𝕋ⁿ: the torus as ℝⁿ/ℤⁿ, Fourier analysis on ℝ and
on 𝕋ⁿ (Plancherel, Parseval), finite differences on ℤⁿ, toroidal symbol classes S^m_{ρ,δ},
toroidal quantization, ellipticity, elliptic regularity for Fourier multipliers, and the
Fredholm property of `(-Δ)^{ν/2} + Q : Hˢ(𝕋ⁿ) → H^{s-ν}(𝕋ⁿ)` (Theorem 3.0.4).
Everything compiles with no `sorry`. The formalization also found an error in equation (1.13)
of the thesis (see below).

## Compilar

```bash
lake exe cache get   # descarga Mathlib precompilada
lake build
```

Versiones: Lean `v4.37.0-rc1`, Mathlib `7dde1da6462d490beca415534c082b4f0435c9a9`
(fijadas en `lean-toolchain`, `lakefile.toml` y `lake-manifest.json`).

## Un error en la tesis encontrado al formalizar

La ecuación (1.13) y la Observación 1.2.5 afirman que `𝕋ⁿ × ℤⁿ ≅ ℝⁿ` como grupos abstractos.
**Es falso** para `n ≥ 1`: el elemento `((½,…,½) + ℤⁿ, 0)` tiene orden 2 en `𝕋ⁿ × ℤⁿ`, y `ℝⁿ`
no tiene torsión. Esto está demostrado en Lean (`not_nonempty_torus_prod_equiv`).

El error está en la prueba: el Corolario 1.2.2 cociente `ℝⁿ × ℤⁿ` por `ℤⁿ × {0}`, y
(1.10)–(1.11) por `ker φ = {0} × ℤⁿ`. Son dos subgrupos **distintos**. Ambos enunciados
correctos están formalizados:

* `(ℝⁿ × ℤⁿ)/(ℤⁿ × {0}) ≅ 𝕋ⁿ × ℤⁿ` (`quotient_lattice_prod_bot`);
* `(ℝⁿ × ℤⁿ)/({0} × ℤⁿ) ≅ ℝⁿ` (`quotient_bot_prod_top`).

## Contenido (tesis → Lean)

| Tesis | Enunciado | Nombre en Lean | Archivo |
|---|---|---|---|
| §1.1.1, (1.2)–(1.5) | `e^{2πiθ} = 1 ⟺ θ ∈ ℤ`; `ker φ = ℤ`; `ℝ/ℤ ≅ 𝕊¹` | `exp_two_pi_I_eq_one_iff`, `ker_expHom`, `addCircleEquivCircle` | `Torus.lean` |
| p. 8 | `𝕋ⁿ = ℝⁿ/ℤⁿ ≅ (ℝ/ℤ)ⁿ` | `torusEquivPi` | `Torus.lean` |
| Teo. 1.2.1 | `(A×B)/(C×D) ≅ A/C × B/D` | `quotientProdEquiv` | `Torus.lean` |
| Ej. 1.2.4 | `𝕋ⁿ` es un grupo topológico compacto Hausdorff | `example` | `Torus.lean` |
| Cor. 1.2.2, (1.13), Obs. 1.2.5 | **corrección**, ver arriba | `not_nonempty_torus_prod_equiv`, … | `Torus.lean` |
| Def. 1.3.1, Ej. 1.3.2 | funciones 1-periódicas; los polinomios trigonométricos lo son | `IsPeriodic`, `trigPoly_periodic` | `Quantization.lean` |
| Ej. 1.4.2 | `𝓕(e^{-πx²}) = e^{-πξ²}` | `fourier_gaussian` | `Fourier.lean` |
| Prop. 1.4.6 (1) | `‖f̂‖_∞ ≤ ‖f‖_{L¹}` | `norm_fourier_le` | `Fourier.lean` |
| Teo. 1.4.8 (2) | fórmula de inversión de Fourier | `fourier_inversion` | `Fourier.lean` |
| Ej. 1.4.13 | `∫ e^{\|x\|²} e^{-\|x\|²} dx` diverge | `not_integrable_exp_sq_mul_gaussian` | `Fourier.lean` |
| Ej. 1.5.3, 1.5.4 | coeficientes de Fourier de `1` y de `e^{2πiξ₀·x}` | `mFourierCoeff_one`, `mFourierCoeff_mFourier` | `Fourier.lean` |
| Prop. 1.5.2 | Plancherel, Parseval, isometría `L²(𝕋ⁿ) ≅ ℓ²(ℤⁿ)` | `plancherel`, `parseval`, `fourier_isometry` | `Fourier.lean` |
| Def. 2.0.5, (2.4)–(2.5) | diferencias `Δ_{ξⱼ}`, `Δ̄_{ξⱼ}`, `Δ^α`, `Δ̄^α` | `fwd`, `bwd`, `fwdMulti`, `bwdMulti`, `fwdMulti_add_single` | `Differences.lean` |
| Ej. 2.0.6 | tabla de valores y `Δ_{ξ₁}Δ_{ξ₂}σ(1,1) = 1` | `ex206_fwd0`, `ex206_fwd1`, `ex206_fwd01`, `ex206_multi` | `Differences.lean` |
| **Prop. 2.0.7** | fórmulas (2.6) y (2.7) para `Δ^α` y `Δ̄^α` | `fwdMulti_eq_sum`, `bwdMulti_eq_sum` | `Differences.lean` |
| Def. 2.0.9 | `⟨ξ⟩` y la clase `S^m_{ρ,δ}(𝕋ⁿ × ℤⁿ)` | `jbr`, `SymbolClass`, `SymbolClass.mono` | `Symbols.lean` |
| Ej. 2.0.10, Obs. 2.0.11–2.0.12 | `Δ_{ξⱼ}⟨ξ⟩² = 2ξⱼ+1`, `Δ²=2`, `Δ³=0`; `⟨ξ⟩² ∈ S²_{1,0}` | `fwd_bracketSq`, `fwdMulti_bracketSq`, `bracketSq_mem_S2` | `Differences.lean`, `Symbols.lean` |
| Def. 2.0.15 | cuantización toroidal `Op(a)` | `Op` | `Quantization.lean` |
| Obs. 2.0.16 | `a(x,ξ) = e^{-2πix·ξ} (Op(a)e_ξ)(x)` | `symbol_eq_of_Op` | `Quantization.lean` |
| p. 35 | `(T_h f)^(ξ) = e^{2πih·ξ} f̂(ξ)`; `-Δ(T_h f) = T_h(-Δ f)` | `trigPoly_translate`, `Op_translate`, `lap_comm_translate` | `Quantization.lean` |
| Cor. 2.0.26 | los multiplicadores de Fourier conmutan con traslaciones | `multiplier_comm_translate` | `Quantization.lean` |
| Ej. 2.0.27 | `2^ν π^ν \|ξ\|^ν = (2π\|ξ\|)^ν` | `fracLap_symbol` | `Quantization.lean` |
| Ej. 2.0.28 | `Op(\|ξ\|² + V) f = Op(\|ξ\|²) f + V f` | `Op_add_potential` | `Quantization.lean` |
| Ej. 2.0.30 | `Op(σ) cos 2πx = √2 (1 + sen 2πx) cos 2πx` | `trigPoly_ex2030`, `Op_ex2030` | `Quantization.lean` |
| Def. 3.0.1 | parametrices: `S = P + R₂P − SR₁` | `left_eq_right_parametrix`, `parametrix_sub_mem` | `Elliptic.lean` |
| Obs. 2.0.20 | espacios de Sobolev `Hˢ(𝕋ⁿ)`, `Hˢ ⊆ Hᵗ` si `t ≤ s` | `InSobolev`, `InSobolev.mono` | `Elliptic.lean` |
| Def. 3.0.2 | elíptico / fuertemente elíptico de orden `m` | `IsElliptic`, `IsStronglyElliptic` | `Elliptic.lean` |
| Ej. 3.0.3 | `-Δ` tiene símbolo `4π²\|ξ\|²` y es elíptico de orden 2 | `Op_lapSymbol`, `lap_stronglyElliptic` | `Quantization.lean`, `Elliptic.lean` |
| Teo. 3.0.4 (elipticidad) | `(-Δ)^{ν/2} + Q(x)` es fuertemente elíptico | `fracLap_add_potential_stronglyElliptic` | `Elliptic.lean` |
| **Teo. 3.0.4 (Fredholm)** | `(-Δ)^{ν/2} + Q : Hˢ(𝕋ⁿ) → H^{s−ν}(𝕋ⁿ)` es Fredholm para todo `s ∈ ℝ` | `isFredholm_sobolevOp` | `Fredholm.lean` |
| Def. 2.0.1 | `S(ℤⁿ)`; `∑ ⟨ξ⟩ᵗ \|φ(ξ)\| < ∞` para `φ ∈ S(ℤⁿ)` | `IsRapidlyDecreasing`, `IsRapidlyDecreasing.summable_weighted` | `Fredholm.lean` |
| (3.9) | regularidad elíptica `f ∈ Hˢ ⇒ u ∈ H^{s+m}` (multiplicadores) | `elliptic_regularity_multiplier` | `Elliptic.lean` |
| Ej. 3.0.5 | `F_{𝕋ⁿ}(Pf)(ξ) = (2π\|ξ\|)^ν f̂(ξ)` | `fourier_fracLap`, `mFourierCoeff_OpT` | `Fourier.lean` |

## La propiedad de Fredholm (Teorema 3.0.4)

`isFredholm_sobolevOp` usa la noción de operador de Fredholm de Mathlib
(`ContinuousLinearMap.IsFredholm`). Se formaliza así:

* `Q ∈ C^∞(𝕋ⁿ)` se describe por sus coeficientes de Fourier `q = Q̂ ∈ S(ℤⁿ)`
  (Def. 2.0.1; la Def. 2.0.3 de la tesis dice que `F_{𝕋ⁿ} : C^∞(𝕋ⁿ) → S(ℤⁿ)` es biyectiva).
  La multiplicación por `Q` es la convolución con `q` (`mFourierCoeff_mul_mFourier`).
* `Hˢ(𝕋ⁿ)` se identifica con `ℓ²(ℤⁿ)` vía `u ↦ (⟨ξ⟩ˢ û(ξ))_ξ` (`inSobolev_iff_memℓp`). En esas
  coordenadas el operador es `sobolevOp`, y `sobolevOp_apply` da su fórmula explícita.
* La prueba no usa el cálculo simbólico: `T = A + ι∘(M_Q − I)` con `A = (−Δ)^{ν/2} + 1`
  invertible, `M_Q` acotado en `Hˢ` (desigualdad de Peetre `weight_ratio_le` y cota de
  Schur/Young `schur_bound`) e `ι : Hˢ ↪ H^{s−ν}` límite en norma de operadores de rango finito
  (Rellich). Así `T = A(I + E + F)` con `‖E‖ < 1` y `F` de rango finito.

Nota: en el enunciado de la tesis dice «de `H^ν(𝕋ⁿ)` en `H^{s−ν}(𝕋ⁿ)`»; debe ser
«de `Hˢ(𝕋ⁿ)` en `H^{s−ν}(𝕋ⁿ)`», que es lo formalizado.

## Convenciones

* Igual que en la Definición 1.3.1, una función en `𝕋ⁿ` es una función 1-periódica en `ℝⁿ`.
  Un símbolo es `a : ℝⁿ → ℤⁿ → ℂ`, 1-periódico y suave en `x`. Para `L²(𝕋ⁿ)` se usa el toro de
  Mathlib, `UnitAddTorus (Fin n) = (ℝ/ℤ)ⁿ`, con la medida de Haar normalizada, y
  `mFourier_coe` conecta ambos puntos de vista.
* Las derivadas `∂^β_x` de orden `|β| = k` se codifican con la `k`-ésima derivada de Fréchet
  (`iteratedFDeriv`), cuya norma es equivalente a `máx_{|β|=k} |∂^β_x a|`.
* `Op(a)` se define sobre polinomios trigonométricos (coeficientes de Fourier de soporte finito);
  `mFourierCoeff_trigPoly` prueba que esos coeficientes son los coeficientes de Fourier del toro.
* `Δ^α` se define con el álgebra de grupo conmutativa `ℤ[ℤⁿ]` que actúa por traslaciones. Es la
  misma idea que la prueba de la Prop. 2.0.7 (`Δⱼ = Eⱼ − I`, binomio multivariado).
  `fwdMulti_add_single` muestra que coincide con la composición `Δ_{ξ₁}^{α₁}⋯Δ_{ξₙ}^{αₙ}`.

## Lo que no está formalizado

Estos resultados se usan o se citan en la tesis, pero necesitan teoría que aún no está en
Mathlib:

* el cálculo simbólico (composición y sumas asintóticas en `Ψ^m_{ρ,δ}`), la construcción
  (3.2)–(3.6) de la parametriz para símbolos que dependen de `x`, y la regularidad (3.9) en ese
  caso general;
* la continuidad `Hˢ → H^{s−m}` de `Op S^m_{ρ,δ}` para símbolos generales, y la equivalencia
  `Q ∈ C^∞(𝕋ⁿ) ⟺ Q̂ ∈ S(ℤⁿ)` (se usa la Def. 2.0.3 de la tesis, sin probarla);
* la Prop. 2.0.19 (símbolos de Hörmander = símbolos toroidales), el Teo. 2.0.22 (representación de
  operadores continuos en `C^∞(𝕋ⁿ)`), la Obs. 2.0.21 y las estructuras de Fréchet
  (Obs. 2.0.13, 2.0.18);
* la fórmula de Leibniz (Obs. 2.0.8) y los ítems restantes de la Prop. 1.4.6 y del Teo. 1.4.8.

## Estructura

```
TorusPsiDO/
  Torus.lean         §1.1–1.2  toro, cocientes, corrección de (1.13)
  Differences.lean   §2        diferencias finitas, Prop. 2.0.7, Ej. 2.0.6, 2.0.10
  Symbols.lean       §2        ⟨ξ⟩, clases S^m_{ρ,δ}, ⟨ξ⟩² ∈ S²_{1,0}
  Quantization.lean  §1.3, §2  polinomios trigonométricos, Op(a), traslaciones, -Δ, Ej. 2.0.30
  Fourier.lean       §1.4–1.5  Gaussiana, inversión, Plancherel/Parseval en 𝕋ⁿ, Ej. 3.0.5
  Elliptic.lean      §3        parametrices, Sobolev, elipticidad, regularidad elíptica
  L2Operators.lean   §3        operadores diagonales y de núcleo en ℓ²(ℤⁿ), cota de Schur
  Fredholm.lean      §3        Peetre, S(ℤⁿ), Teorema 3.0.4: propiedad de Fredholm
```
