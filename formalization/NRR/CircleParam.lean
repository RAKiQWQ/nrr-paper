import NRR.AngularLoops

/-! The standard interval parametrization of the circle is a quotient.
Closed paths therefore give actual continuous circle maps, with their
parametrized values and winding preserved exactly. -/

noncomputable section
open Topology
open scoped unitInterval

namespace NRR.Surface

theorem periodPath_quotient : IsQuotientMap periodPath :=
  periodPath.continuous.isClosedMap.isQuotientMap periodPath.continuous
    periodPath_surjective

def descendClosed {X : Type*} [TopologicalSpace X] (p : C(I, X))
    (closed : p 0 = p 1) : C(Circle, X) :=
  periodPath_quotient.lift p (by
    intro t u h
    rcases periodPath_fiber h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [rfl, closed, closed.symm])

@[simp] theorem descendClosed_comp {X : Type*} [TopologicalSpace X]
    (p : C(I, X)) (closed : p 0 = p 1) :
    (descendClosed p closed).comp periodPath = p :=
  periodPath_quotient.lift_comp p _

@[simp] theorem descendClosed_period {X : Type*} [TopologicalSpace X]
    (p : C(I, X)) (closed : p 0 = p 1) (t : I) :
    descendClosed p closed (periodPath t) = p t :=
  congrArg (fun g : C(I, X) => g t) (descendClosed_comp p closed)

def circleOfPath {X : Type*} [TopologicalSpace X] {a : X}
    (p : Path a a) : C(Circle, X) :=
  descendClosed p.toContinuousMap (by change p 0 = p 1; rw [Path.source, Path.target])

@[simp] theorem circleOfPath_period {X : Type*} [TopologicalSpace X] {a : X}
    (p : Path a a) (t : I) : circleOfPath p (periodPath t) = p t :=
  descendClosed_period _ _ _

theorem winding_circleOfPath {X : Type} [TopologicalSpace X] {a : X}
    (p : Path a a) (f : C(X, Circle)) :
    winding (f.comp (circleOfPath p)) = AngularLoops.increment f p := by
  unfold winding AngularLoops.increment
  congr 1
  ext t
  exact congrArg (fun x : X => (f x : ℂ)) (circleOfPath_period p t)

end NRR.Surface
