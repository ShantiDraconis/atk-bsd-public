import Mathlib
import ATK.Exact
import ATK.BSDBridge

/-!
# ATK — Linha de explosão para BSD

Adaptação da linha de explosão do NS (testemunha / refutação / dicotomia):

* **testemunha de explosão** `RankDiscrepancy`: uma curva elíptica `E/ℚ` e uma continuação
  inteira `L` da sua série L cuja ordem de anulação em `s = 1` NÃO é o posto de `E(ℚ)`
  (ordem infinita, ou finita e diferente);
* **refutação** `explosion_refutes : RankDiscrepancy → ¬ BSDRank` — usa a unicidade da
  continuação (`continuation_unique`), então não importa qual `L` o alvo escolheria;
* **dicotomia** (dada a continuação H1) `bsd_iff_no_explosion : BSDRank ↔ IsEmpty RankDiscrepancy`.

Nenhuma testemunha é conhecida. Para ordem analítica ≤ 1 a igualdade é teorema (Gross–Zagier,
Kolyvagin; não formalizado), então uma explosão exigiria ordem analítica ≥ 2.
-/

noncomputable section

namespace ATK.BSDExplosion

open ATK.BSDBridge

/-- Testemunha de explosão: discrepância entre ordem de anulação e posto. -/
structure RankDiscrepancy where
  E : WeierstrassCurve ℚ
  ell : E.IsElliptic
  L : ℂ → ℂ
  entire : Differentiable ℂ L
  agree : ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s
  mismatch : ¬ ∃ r : ℕ, analyticOrderAt L 1 = r ∧ Module.rank ℤ E.toAffine.Point = r

theorem explosion_refutes (w : RankDiscrepancy) : ¬ BSDRank := by
  intro h
  haveI := w.ell
  obtain ⟨L', hL', hag', hr⟩ := h w.E
  have hLL : L' = w.L := continuation_unique hL' w.entire hag' w.agree
  rw [hLL] at hr
  exact w.mismatch hr

/-- Dicotomia, dada a continuação analítica (H1). -/
theorem bsd_iff_no_explosion (hC : AnalyticContinuation) :
    BSDRank ↔ IsEmpty RankDiscrepancy := by
  constructor
  · intro h
    exact ⟨fun w => explosion_refutes w h⟩
  · intro h
    rw [bsd_iff_rankEquality hC]
    intro E hE L hL hag
    by_contra hne
    exact h.1 ⟨E, hE, L, hL, hag, hne⟩

end ATK.BSDExplosion

end

#print axioms ATK.BSDExplosion.explosion_refutes
#print axioms ATK.BSDExplosion.bsd_iff_no_explosion
