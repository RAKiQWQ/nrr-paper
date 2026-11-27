import NRR.Binomial
import Mathlib.Data.Finset.Powerset

/-! Exact signed ray crossings for the six-piece polygon.
Coordinates have been multiplied by 24 so all vertices are integral.
The integer computations do not assume degree or extension theorems. -/

namespace NRR.Six

abbrev Point := ℤ × ℤ

def diamond (c : ℤ) (counterclockwise : Bool) : List Point :=
  if counterclockwise then [(c-1,0),(c,-1),(c+1,0),(c,1)]
  else [(c+1,0),(c,-1),(c-1,0),(c,1)]

def half : List Point :=
  [(0,1),(16,1)] ++ diamond 16 false ++ diamond 16 false ++
  [(0,1),(8,1)] ++ diamond 8 false ++ diamond 8 false ++
  [(0,1)] ++ diamond 0 true ++ [(1,0),(0,-1)]

def polygon : List Point := half ++ half.tail.map (fun p => (-p.1,-p.2))

def orient (c : ℤ) (a b : Point) : ℤ :=
  (b.1-a.1)*(-a.2) - (b.2-a.2)*(c-a.1)

/-- Half-open ray crossing convention counts a vertex only once. -/
def crossing (c : ℤ) (a b : Point) : ℤ :=
  if a.2 ≤ 0 ∧ 0 < b.2 ∧ 0 < orient c a b then 1
  else if b.2 ≤ 0 ∧ 0 < a.2 ∧ orient c a b < 0 then -1 else 0

def through (c : ℤ) (a b : Point) : Bool :=
  decide (orient c a b = 0 ∧ min a.1 b.1 ≤ c ∧ c ≤ max a.1 b.1 ∧
    min a.2 b.2 ≤ 0 ∧ 0 ≤ max a.2 b.2)

def edges : List (Point × Point) := polygon.zip polygon.tail

def puncture (j : ℕ) : ℤ := 24 - 8 * (j : ℤ)

def degreeEntry (j : ℕ) : ℤ :=
  if j = 0 ∨ j = 6 then 1
  else 1 + (edges.map (fun (a,b) => crossing (puncture j) a b)).sum

theorem misses_all_punctures :
    ∀ j : Fin 5, edges.any (fun (a,b) => through (puncture (j.val+1)) a b) = false := by
  decide

theorem degree_entries : (List.range 7).map degreeEntry = [1,-1,-1,2,-1,-1,1] := by
  decide

/-- Fix the first root's sign. The remaining four signs enumerate the sixteen ends. -/
def ends := (Finset.univ : Finset (Fin 4)).powerset

def endDegree (s : Finset (Fin 4)) := degreeEntry (1+s.card) + degreeEntry (2+s.card)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem distribution :
    (ends.filter (fun s => endDegree s = -2)).card = 5 ∧
    (ends.filter (fun s => endDegree s = 1)).card = 10 ∧
    (ends.filter (fun s => endDegree s = 0)).card = 1 ∧
    ∑ s ∈ ends, endDegree s = 0 := by
  decide

end NRR.Six
