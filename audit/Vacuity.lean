/-!
# Auditoria de vacuidade — `MCore.Material.BSDClosure`

A estrutura abaixo é cópia verbatim de `imports/lean/MCore/Material/Closure.lean` (o original
importa `MCore`, mas a estrutura não usa nada de lá; aqui só o Lean core).

Resultado certificado pelo kernel: `MaterialBSDProducer R T Q` é EXATAMENTE `R ∧ T ∧ Q`. A
estrutura não contém matemática de BSD: todo o conteúdo está nas três proposições passadas como
parâmetro. Com `True` ela vale; com `False` ela falha. Enquanto `R`, `T`, `Q` não forem os
enunciados reais (posto = ordem de anulação de `L(E,s)` em `s = 1`, e a fórmula do coeficiente
líder), um habitante não diz nada sobre BSD. Esses enunciados não são expressáveis na
Mathlib v4.34.1 (falta `L(E,s)` com continuação analítica). Estado: **CONDICIONAL**.
-/

namespace Audit.BSD

structure BSDClosure (RankResidual Torsion Quotient : Prop) where
  rankResidual : RankResidual
  torsionPositive : Torsion
  quotientIdentity : Quotient

def MaterialBSDProducer (RankResidual Torsion Quotient : Prop) : Prop :=
  Nonempty (BSDClosure RankResidual Torsion Quotient)

/-- O produtor é exatamente a conjunção dos parâmetros. -/
theorem producer_iff (R T Q : Prop) : MaterialBSDProducer R T Q ↔ (R ∧ T ∧ Q) :=
  ⟨fun ⟨h⟩ => ⟨h.rankResidual, h.torsionPositive, h.quotientIdentity⟩,
   fun ⟨r, t, q⟩ => ⟨⟨r, t, q⟩⟩⟩

/-- Vacuidade: com parâmetros triviais o "fechamento" vale sem matemática alguma. -/
theorem producer_trivial : MaterialBSDProducer True True True :=
  ⟨⟨trivial, trivial, trivial⟩⟩

/-- E com um parâmetro falso ele falha: o conteúdo está todo nos parâmetros. -/
theorem producer_false (T Q : Prop) : ¬ MaterialBSDProducer False T Q :=
  fun ⟨h⟩ => h.rankResidual

end Audit.BSD

#print axioms Audit.BSD.producer_iff
#print axioms Audit.BSD.producer_trivial
#print axioms Audit.BSD.producer_false
