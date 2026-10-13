# Estado: CONDICIONAL — Birch e Swinnerton-Dyer

Auditoria de 13/10/2026 sobre o commit `3301d55` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

Para toda curva elíptica `E/ℚ`: `posto E(ℚ) = ord_{s=1} L(E, s)`, e o coeficiente líder de
`L(E, s)` em `s = 1` é dado pela fórmula BSD (período, regulador, Tamagawa, `Ш`, torção).

A Mathlib v4.34.1 tem curvas de Weierstrass e a lei de grupo, mas não a função `L(E, s)` com
continuação analítica até `s = 1`. **Estado no portão: NÃO_ENUNCIÁVEL.**

## 2. Varredura do conteúdo

1 arquivo Lean · 0 `axiom` · 0 `sorry`/`admit`. `CERTIFICATES/FINAL_REPRO.md` ("GREEN") certifica
build, firewall e reprodutibilidade — o próprio arquivo diz que não afirma prova de BSD.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Por que é condicional | O que fechar |
|---|---|---|---|
| D1 | `BSDClosure R T Q` / `MaterialBSDProducer` (`imports/lean/MCore/Material/Closure.lean`) | **Certificado pelo kernel** (`audit/Vacuity.lean`): `MaterialBSDProducer R T Q ↔ R ∧ T ∧ Q` (`producer_iff`); vale com `True` (`producer_trivial`) e falha com `False` (`producer_false`). Todo o conteúdo está nos três parâmetros | Fixar `R`, `T`, `Q` como os enunciados reais (igualdade de posto; positividade/finitude da torção; identidade do coeficiente líder) |
| D2 | Enunciados reais | Dependem de `L(E, s)` e de `Ш` | Formalizar `L(E, s)` com continuação analítica (via modularidade) — fundação anterior ao problema |
| D3 | "realizable elliptic-curve domain" (alvo registrado em `atk-math-core-public`, 3 átomos) | Mesmo diagnóstico de D1: conjunção de três alvos abertos | Idem D1/D2 |
| D4 | Numérica (reticulado de Mordell–Weil, M-Core `m-core-bsd/bsd_lattice`) | Evidência por curva, não teorema universal | Manter como evidência; não contar como fechamento |
| D5 | Compilação | `Closure.lean` importa `MCore`, ausente aqui. (`audit/Vacuity.lean` compila só com Lean core — workflow `vacuity-check`) | CI a partir do commit de origem (`provenance/`) |

## 4. Falsificador exato

Uma curva `E/ℚ` com `posto E(ℚ) ≠ ord_{s=1} L(E, s)`, ou com coeficiente líder diferente da
fórmula BSD. Não enunciável na Mathlib v4.34.1.

## 5. Condição para mudar o estado

NÃO_ENUNCIÁVEL → ABERTO quando `L(E, s)` e os termos da fórmula forem formalizados; só então um
fechamento pode ser avaliado pelo portão.

---

**English summary.** Status CONDITIONAL / gate NOT STATABLE (no `L(E,s)` with analytic
continuation in Mathlib). Kernel-certified finding: `MaterialBSDProducer R T Q` is exactly
`R ∧ T ∧ Q` — it holds for `True` and fails for `False`; all content lives in the parameters,
which must become the real BSD statements.
