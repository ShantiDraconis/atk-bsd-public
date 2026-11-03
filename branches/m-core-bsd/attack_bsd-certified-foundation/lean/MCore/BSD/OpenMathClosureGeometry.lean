import MCore.BSD.RealizableRankFrontier

namespace MCore

/-- Three-state branch used only for OPEN_MATH frontier bookkeeping.
    A branch is either unresolved, or resolved true/false. -/
inductive FrontierBranchState where
  | open
  | trueBranch
  | falseBranch
deriving DecidableEq, Repr

/-- The four terminal signatures. Mixed truth values are still fully closed. -/
inductive FrontierTerminalSignature where
  | TT | TF | FT | FF
deriving DecidableEq, Repr

def branchClosed : FrontierBranchState → Bool
  | .open => false
  | .trueBranch => true
  | .falseBranch => true

def unresolvedWeight : FrontierBranchState → Nat
  | .open => 1
  | .trueBranch => 0
  | .falseBranch => 0

/-- Exact discrete distance to the terminal set, in unresolved branches.
    0 = fully closed, 1 = half unresolved, 2 = fully unresolved. -/
def frontierDistance (a b : FrontierBranchState) : Nat :=
  unresolvedWeight a + unresolvedWeight b

/-- Closure percentage for the two-branch model: 0, 50, or 100. -/
def frontierClosurePercent (a b : FrontierBranchState) : Nat :=
  100 - 50 * frontierDistance a b

def terminalSignature? :
    FrontierBranchState → FrontierBranchState → Option FrontierTerminalSignature
  | .trueBranch,  .trueBranch  => some .TT
  | .trueBranch,  .falseBranch => some .TF
  | .falseBranch, .trueBranch  => some .FT
  | .falseBranch, .falseBranch => some .FF
  | _, _ => none

def frontierClosed (a b : FrontierBranchState) : Prop :=
  terminalSignature? a b ≠ none

theorem TT_is_closed :
    frontierClosed .trueBranch .trueBranch := by
  decide

theorem TF_is_closed :
    frontierClosed .trueBranch .falseBranch := by
  decide

theorem FT_is_closed :
    frontierClosed .falseBranch .trueBranch := by
  decide

theorem FF_is_closed :
    frontierClosed .falseBranch .falseBranch := by
  decide

theorem closed_iff_distance_zero (a b : FrontierBranchState) :
    frontierClosed a b ↔ frontierDistance a b = 0 := by
  cases a <;> cases b <;> decide

theorem closed_implies_100_percent (a b : FrontierBranchState)
    (h : frontierClosed a b) :
    frontierClosurePercent a b = 100 := by
  rw [closed_iff_distance_zero] at h
  simp [frontierClosurePercent, h]

theorem one_open_is_50_percent (a : FrontierBranchState)
    (ha : branchClosed a = true) :
    frontierClosurePercent a .open = 50 := by
  cases a <;> simp [branchClosed] at ha ⊢

theorem open_open_is_0_percent :
    frontierClosurePercent .open .open = 0 := by
  decide

/-- The closure theorem: OPEN_MATH disappears exactly when both branches
    have left the unresolved state. Truth polarity determines the terminal
    signature, not the degree of closure. -/
theorem frontier_closure_theorem (a b : FrontierBranchState) :
    frontierClosed a b ↔
      branchClosed a = true ∧ branchClosed b = true := by
  cases a <;> cases b <;> decide

/-- Abstract force parameters. They do not assert mathematical truth; they
    record which side each force currently supports. -/
structure FrontierForces where
  torsion : Int
  tension : Int
  contraction : Int
  rotation : Int
deriving Repr

/-- Net signed tendency. Positive and negative are terminal directions;
    zero is the undecided boundary. -/
def netFrontierForce (f : FrontierForces) : Int :=
  f.torsion + f.tension + f.contraction + f.rotation

def forceState (f : FrontierForces) : FrontierBranchState :=
  if 0 < netFrontierForce f then .trueBranch
  else if netFrontierForce f < 0 then .falseBranch
  else .open

theorem nonzero_force_resolves_branch (f : FrontierForces)
    (h : netFrontierForce f ≠ 0) :
    branchClosed (forceState f) = true := by
  unfold forceState
  by_cases hp : 0 < netFrontierForce f
  · simp [hp, branchClosed]
  · have hn : netFrontierForce f < 0 := by omega
    simp [hp, hn, branchClosed]

theorem two_nonzero_forces_close_open_math
    (f g : FrontierForces)
    (hf : netFrontierForce f ≠ 0)
    (hg : netFrontierForce g ≠ 0) :
    frontierClosed (forceState f) (forceState g) := by
  rw [frontier_closure_theorem]
  exact ⟨nonzero_force_resolves_branch f hf,
         nonzero_force_resolves_branch g hg⟩

#print axioms MCore.frontier_closure_theorem
#print axioms MCore.closed_iff_distance_zero
#print axioms MCore.two_nonzero_forces_close_open_math

end MCore
