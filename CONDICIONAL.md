# Estado: CONDICIONAL — Birch e Swinnerton-Dyer

Auditoria de 13/10/2026 sobre o commit `3301d55` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

Para toda curva elíptica `E/ℚ`: `posto E(ℚ) = ord_{s=1} L(E, s)`, e o coeficiente líder de
`L(E, s)` em `s = 1` é dado pela fórmula BSD (período, regulador, Tamagawa, `Ш`, torção).

**Mudança de estado.** A Mathlib v4.34.1 define a série L de uma curva de Weierstrass sobre um
corpo de números, com os fatores locais corretos em todo primo (via modelo minimal):
`WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`. Com isso a forma oficial do Clay
(posto = ordem de anulação em `s = 1`) **ficou enunciável**: `ATK.BSDBridge.BSDRank`. O que a
Mathlib não tem é a continuação analítica — que entra como hipótese (H1), como no NS.

### Ponte no formato NS — certificada no kernel

| Peça | Declaração (`audit/lean/ATK/BSDBridge.lean`) |
|---|---|
| Alvo exato | `BSDRank`: toda `E/ℚ` elíptica tem `L` inteira igual a `E.LSeries` em `Re s > 3/2`, com `ord_{s=1} L = r` finito e `Module.rank ℤ E(ℚ) = r` |
| Hipótese H | `H_BSD := AnalyticContinuation ∧ RankEquality` |
| Ponte | `bsd_of_H : H_BSD → BSDRank` |
| Bem-posto | `continuation_unique`: a continuação é única (princípio da identidade) — o alvo não escolhe `L` livremente |
| Força de H | H1 (continuação) = **teorema publicado e aceito** (modularidade: Wiles, Taylor–Wiles, BCDT), **não formalizado** — análogo do NS; H2 (posto) = **aberto**; com H1, `BSDRank ↔ RankEquality` (`bsd_iff_rankEquality`) |
| Programa | `bsd_of_material`: `BSDClosure` com o 1º parâmetro fixado em `H_BSD` alimenta a ponte |
| Kernel | **5/5 CERTIFIED** — Lean 4.34.1 + Mathlib v4.34.1 (workflow `audit-kernel`) |

**Estado no portão: CONDICIONAL** — alvo exato; H1 com prova externa não formalizada; H2 em aberto.

### Linha de explosão — certificada no kernel

| Peça | Declaração (`audit/lean/ATK/BSDExplosion.lean`) |
|---|---|
| Testemunha de explosão | `RankDiscrepancy`: curva `E/ℚ` + continuação inteira `L` com `ord_{s=1} L ≠ posto` |
| Refutação | `explosion_refutes : RankDiscrepancy → ¬ BSDRank` (usa a unicidade da continuação) |
| Dicotomia | `bsd_iff_no_explosion : AnalyticContinuation → (BSDRank ↔ IsEmpty RankDiscrepancy)` |
| Estado | **nenhuma testemunha conhecida**; para ordem ≤ 1 a igualdade é teorema (Gross–Zagier, Kolyvagin), logo uma explosão exigiria ordem analítica ≥ 2 |

### Linha de fechamento — CLOSED_MATH calculado pelo kernel

Mesmo formato das linhas condicional e de explosão: **alvo exato** → **certificado** (declaração
sem hipóteses, de tipo exatamente o alvo) → **portão** (`audit/lean/scripts/closure_gate.py`:
kernel + axiomas padrão + controles) → **bandeira** calculada, nunca escrita à mão.

| Alegação | Alvo exato | CLOSED_MATH | Certificado | Rotas certificadas até ela |
|---|---|---|---|---|
| BSD | `ATK.BSDBridge.BSDRank` | **false** | — | ponte `bsd_of_H` (H1 não formalizada, H2 aberta) |
| ¬BSD | `¬ ATK.BSDBridge.BSDRank` | **false** | — | explosão `explosion_refutes` (sem testemunha) |

Controles do portão (todos OK, run `38387846055`): aceita uma decisão verdadeira de problema-brinquedo;
recusa alvo como `axiom`; recusa `sorry`; recusa a ponte e a linha de explosão oferecidas como
certificado (falta H / falta a testemunha); recusa `alvo ∨ ¬alvo` (teorema vazio).

Para mudar uma bandeira para `true`, basta acrescentar a `audit/lean/closure/registry.json`
uma declaração que o kernel aceite com o tipo exato — vinda de uma prova de H (pela ponte) ou de
uma testemunha (pela explosão). Nenhuma outra edição altera o resultado.

## 2. Varredura do conteúdo

1 arquivo Lean · 0 `axiom` · 0 `sorry`/`admit`. `CERTIFICATES/FINAL_REPRO.md` ("GREEN") certifica
build, firewall e reprodutibilidade — o próprio arquivo diz que não afirma prova de BSD.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Por que é condicional | O que fechar |
|---|---|---|---|
| D1 | `BSDClosure R T Q` / `MaterialBSDProducer` (`imports/lean/MCore/Material/Closure.lean`) | **Certificado pelo kernel** (`audit/Vacuity.lean`): `MaterialBSDProducer R T Q ↔ R ∧ T ∧ Q` (`producer_iff`); vale com `True` (`producer_trivial`) e falha com `False` (`producer_false`). Todo o conteúdo está nos três parâmetros | Fixar `R`, `T`, `Q` como os enunciados reais (igualdade de posto; positividade/finitude da torção; identidade do coeficiente líder) |
| D2 | Enunciados reais | Posto: **feito** (`BSDRank`, seção 0). Coeficiente líder (forma refinada, não exigida pelo Clay) ainda depende de `Ш`, regulador e períodos | Formalizar H1 (continuação, via modularidade); para a forma refinada, `Ш` e o regulador |
| D3 | "realizable elliptic-curve domain" (alvo registrado em `atk-math-core-public`, 3 átomos) | Mesmo diagnóstico de D1: conjunção de três alvos abertos | Idem D1/D2 |
| D4 | Numérica (reticulado de Mordell–Weil, M-Core `m-core-bsd/bsd_lattice`) | Evidência por curva, não teorema universal | Manter como evidência; não contar como fechamento |
| D5 | Compilação | `Closure.lean` importa `MCore`, ausente aqui. (`audit/Vacuity.lean` compila só com Lean core — workflow `vacuity-check`) | CI a partir do commit de origem (`provenance/`) |

## 4. Falsificador exato

Uma curva `E/ℚ` com `posto E(ℚ) ≠ ord_{s=1} L(E, s)` — agora enunciável: refuta `RankEquality` e, dada
H1, `BSDRank` (`bsd_iff_rankEquality`). O coeficiente líder diferente da fórmula BSD refuta só a
forma refinada.

## 5. Condição para mudar o estado

CONDICIONAL → FECHADO somente com uma declaração de tipo `BSDRank` aceita pelo portão (o que exige
H1 formalizada e H2 provada), sem `sorry` e só com os axiomas padrão.

---

**English summary.** Status CONDITIONAL. BSD became statable: Mathlib v4.34.1 has the L-series of
an elliptic curve, so the Clay rank form is `BSDRank`, with a kernel-checked bridge
`AnalyticContinuation ∧ RankEquality → BSDRank` (5/5). H1 is modularity (published, not
formalized); H2 is open. Kernel-certified finding: `MaterialBSDProducer R T Q` is exactly
`R ∧ T ∧ Q` — it holds for `True` and fails for `False`; all content lives in the parameters,
which must become the real BSD statements.
