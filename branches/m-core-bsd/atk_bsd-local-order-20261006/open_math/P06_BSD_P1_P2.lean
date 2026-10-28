import P06.BSD.ConcreteBSDProducer

namespace P06.BSD.OpenMath

/-
Legacy OPEN_MATH boundary rewritten fail-closed.

No universal BSD inhabitant is manufactured here.  The two exact material
obligations are named as propositions, and terminal closure is exposed only as
a conditional theorem consuming genuine inhabitants.
-/

variable (M : P06.BSD.ConcreteBSDModel)

/-- Exact universal P1 obligation. -/
abbrev BSDP1OpenMath : Prop := P06.BSD.BSDP1 M

/-- Exact universal P2 obligation. -/
abbrev BSDP2OpenMath : Prop := P06.BSD.BSDP2 M

/-- Mechanical terminal assembly from genuine P1 and P2 inhabitants. -/
theorem bsd_terminal_from_open_math
    (hP1 : BSDP1OpenMath M)
    (hP2 : BSDP2OpenMath M) :
    P06.BSD.BSDTerminal M :=
  P06.BSD.terminal_of_p1_p2 hP1 hP2

#check BSDP1OpenMath
#check BSDP2OpenMath
#check bsd_terminal_from_open_math

end P06.BSD.OpenMath
