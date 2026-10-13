import Mathlib
import ATK.Exact

/-!
# ATK — Birch e Swinnerton-Dyer: alvo exato e ponte condicional (formato da ponte NS)

**Mudança de estado.** A Mathlib v4.34.1 define a função L de uma curva de Weierstrass sobre um
corpo de números, com os fatores locais corretos em todo primo (bom, multiplicativo
cindido/não cindido, aditivo — via modelo minimal): `WeierstrassCurve.LFunction` e
`WeierstrassCurve.LSeries` (`Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`). Com isso a
forma oficial do Clay (Wiles: `L(E,s) = c(s−1)^r + …`, `c ≠ 0`, `r = posto E(ℚ)`) **passa a ser
enunciável**: `BSDRank` abaixo.

* **Alvo exato** `BSDRank`: para toda curva elíptica `E/ℚ` existe `L` inteira que coincide com a
  série L de `E` em `Re s > 3/2` e cuja ordem de anulação em `s = 1` é finita e igual ao posto
  (`Module.rank ℤ E(ℚ)`).
* **Hipótese H** = `AnalyticContinuation ∧ RankEquality`:
  - `AnalyticContinuation` — existência da continuação inteira: **teorema publicado e aceito**
    (modularidade: Wiles, Taylor–Wiles, Breuil–Conrad–Diamond–Taylor), ainda **não formalizado**.
    É o análogo exato da situação NS: hipótese com prova externa, fora do kernel;
  - `RankEquality` — ordem = posto: o **conteúdo aberto** (conhecido para ordem analítica ≤ 1 por
    Gross–Zagier e Kolyvagin; aberto em geral).
* **Ponte**: `bsd_of_H : H_BSD → BSDRank`.

Bem-posto: `continuation_unique` — a continuação, se existe, é única (princípio da identidade);
logo `BSDRank` não escolhe `L` livremente. A estrutura `BSDClosure` do programa
(`imports/lean/MCore/Material/Closure.lean`), com os parâmetros fixados em `H_BSD`, alimenta a
mesma ponte (`bsd_of_material`).
-/

noncomputable section

namespace ATK.BSDBridge

open Complex Filter Topology

/-- **Alvo exato** (forma oficial do Clay, parte do posto). -/
def BSDRank : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ (∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s) ∧
      ∃ r : ℕ, analyticOrderAt L 1 = r ∧ Module.rank ℤ E.toAffine.Point = r

/-- H1 — continuação inteira da série L (modularidade; publicada, não formalizada). -/
def AnalyticContinuation : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- H2 — igualdade entre ordem de anulação em `s = 1` e posto (conteúdo aberto). -/
def RankEquality : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (L : ℂ → ℂ), Differentiable ℂ L →
    (∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s) →
      ∃ r : ℕ, analyticOrderAt L 1 = r ∧ Module.rank ℤ E.toAffine.Point = r

/-- **Hipótese H**. -/
def H_BSD : Prop := AnalyticContinuation ∧ RankEquality

/-- **Ponte certificada** `H → alvo exato`. -/
theorem bsd_of_H (h : H_BSD) : BSDRank := by
  obtain ⟨hC, hR⟩ := h
  intro E _
  obtain ⟨L, hL, hagree⟩ := hC E
  exact ⟨L, hL, hagree, hR E L hL hagree⟩

/-- O alvo implica H1 (a continuação faz parte do enunciado oficial). -/
theorem continuation_of_bsd (h : BSDRank) : AnalyticContinuation := by
  intro E _
  obtain ⟨L, hL, hagree, -⟩ := h E
  exact ⟨L, hL, hagree⟩

/-- **Bem-posto**: duas funções inteiras que coincidem com a série L em `Re s > 3/2` são iguais. -/
theorem continuation_unique {E : WeierstrassCurve ℚ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : Differentiable ℂ L₁) (h₂ : Differentiable ℂ L₂)
    (a₁ : ∀ s : ℂ, 3 / 2 < s.re → L₁ s = E.LSeries s)
    (a₂ : ∀ s : ℂ, 3 / 2 < s.re → L₂ s = E.LSeries s) : L₁ = L₂ := by
  have hU : {s : ℂ | 3 / 2 < s.re} ∈ 𝓝 (2 : ℂ) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
    show (3 / 2 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ := by
    filter_upwards [hU] with s hs
    rw [a₁ s hs, a₂ s hs]
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => h₁.analyticAt z)
    (fun z _ => h₂.analyticAt z) hev

/-- Com a continuação (H1), H2 é exatamente o que falta: `BSDRank ↔ RankEquality`. -/
theorem bsd_iff_rankEquality (hC : AnalyticContinuation) : BSDRank ↔ RankEquality := by
  constructor
  · intro h E _ L hL hagree
    obtain ⟨L', hL', hagree', hr⟩ := h E
    have hLL : L' = L := continuation_unique hL' hL hagree' hagree
    rw [← hLL]
    exact hr
  · intro hR
    exact bsd_of_H ⟨hC, hR⟩

/-- Cópia verbatim de `MCore.Material.BSDClosure` / `MaterialBSDProducer`. -/
structure BSDClosure (RankResidual Torsion Quotient : Prop) where
  rankResidual : RankResidual
  torsionPositive : Torsion
  quotientIdentity : Quotient

def MaterialBSDProducer (RankResidual Torsion Quotient : Prop) : Prop :=
  Nonempty (BSDClosure RankResidual Torsion Quotient)

/-- A estrutura do programa, com o primeiro parâmetro fixado em `H_BSD`, alimenta a ponte. -/
theorem bsd_of_material {T Q : Prop} (h : MaterialBSDProducer H_BSD T Q) : BSDRank := by
  obtain ⟨c⟩ := h
  exact bsd_of_H c.rankResidual

end ATK.BSDBridge

end

#print axioms ATK.BSDBridge.bsd_of_H
#print axioms ATK.BSDBridge.continuation_of_bsd
#print axioms ATK.BSDBridge.continuation_unique
#print axioms ATK.BSDBridge.bsd_iff_rankEquality
#print axioms ATK.BSDBridge.bsd_of_material
