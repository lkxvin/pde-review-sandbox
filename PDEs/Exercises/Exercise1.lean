import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Integral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Normed.Affine.Isometry

open MeasureTheory Set Topology Metric Filter
open scoped BigOperators ENNReal
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
variable {n : ℕ}
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false

/- Takes the last index of an indexing set Fin n = {0,...,n-1} -/

def lastIdx (h : n ≥ 1) : Fin n := ⟨n - 1, by omega⟩

/- Takes a number i from {0,...,n-2} and lets us use it in {0,...,n-1} -/

def dropLast (h : n ≥ 1) (i : Fin (n - 1)) : Fin n := ⟨i.val , by omega⟩

 /- We have a graph g from ℝ(n-1) to ℝ , take a point p, if the last entry of p is equal to g(*first n-1 entries*), then  p is on the graph of g -/

def graphInRn (h : n ≥ 1) (g: EuclideanSpace ℝ (Fin (n - 1)) → ℝ) :
Set (EuclideanSpace ℝ (Fin n)) := {p | p (lastIdx h) = g ((WithLp.equiv 2 _).symm (fun i => p (dropLast h i))) }
/- Here we are defining that if p is below the graph of g, then p is in the subgraph of g.
This becomes useful later when we define the orientation of U ∩ Ω -/

def strictSubgraphInRn (h : n ≥ 1) (g : EuclideanSpace ℝ (Fin (n - 1)) → ℝ) :
Set (EuclideanSpace ℝ (Fin n)) := { p | p (lastIdx h) < g ((WithLp.equiv 2 _).symm (fun i => p (dropLast h i))) }

noncomputable def northPole (h : n ≥ 1) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 _).symm (Pi.single (lastIdx h) (1 : ℝ))

def HasC1Boundary (h : n ≥ 1) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
∀ x₀ ∈ frontier Ω,
  ∃ (T : (EuclideanSpace ℝ (Fin n)) ≃ᵃⁱ[ℝ] (EuclideanSpace ℝ (Fin n)))
    (V : Set (EuclideanSpace ℝ (Fin (n - 1))))
    (g : EuclideanSpace ℝ (Fin (n - 1)) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))),
    IsOpen V ∧ /- Condition 1: V is open -/
    ContDiffOn ℝ 1 g V ∧  /- Condition 2: g is C1 on V -/
    IsOpen U ∧ /- Condition 3: U is open -/
    x₀ ∈ U ∧ /- Condition 4: x₀ is in U -/
    frontier Ω ∩ U = T '' graphInRn h g ∩ U ∧ /-(The image of the graph of g under T) ∩ U = ∂Ω ∩ U -/
    Ω ∩ U = T '' strictSubgraphInRn h g ∩ U  /- T(subgraph of g) = Ω ∩ U -/

/-  Maybe later can use T.linearIsometryEquic.toLinearEquivdet = 1 to get rid of reflection -/


/-

Exercise 1:  take a unit circle in ℝ(2 or 3) and use the definition above and show that the circle / sphere has C1 boundary
1. Need to define sphere
2. to show that it has C1 boundary, need to find T,g,U and show that it satisfies the conditions above.
-/

/- ---------------------------------------------------------------------------------------- -/

-- Definition of unit sphere in mathlib
def unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=  -- the unit sphere {x | ‖x‖ = 1} in ℝⁿ
  Metric.sphere 0 1                                         -- Mathlib's metric sphere: centre 0, radius 1

-- Definition of unit ball in mathlib
def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=    -- the open unit ball {x | ‖x‖ < 1} in ℝⁿ
  Metric.ball 0 1                                           -- Mathlib's metric ball: centre 0, radius 1 (open, so excludes the sphere)

-- The frontier of the open unit ball is the unit sphere
lemma frontier_unitBall (hn : n ≥ 1) :
    frontier (unitBall n) = unitSphere n := by              -- claim: the topological boundary ∂(ball) is exactly the sphere
  dsimp [unitBall, unitSphere]                              -- unfold both definitions to `Metric.ball`/`Metric.sphere`
  exact frontier_ball 0 (by norm_num)                       -- Mathlib's `frontier_ball`: ∂(ball c r) = sphere c r when r ≠ 0 (here r = 1)

noncomputable def heightFunction (h : n ≥ 1) :
    EuclideanSpace ℝ (Fin (n - 1)) → ℝ :=                   -- maps a point y of the equatorial ℝⁿ⁻¹ to a height in ℝ
  fun y => Real.sqrt (1 - ‖y‖^2)                            -- g(y) = √(1 − ‖y‖²): the height of the upper hemisphere over y

lemma heightFunction_contDiffOn (h : n ≥ 1) :
    ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n - 1)) =>
      Real.sqrt (1 - ‖y‖^2)) (Metric.ball 0 1) := by        -- claim: g is C¹ on the open unit ball (where the radicand stays positive)
  -- Split the goal into smoothness and the non-zero constraint
  apply ContDiffOn.sqrt                                     -- √(f) is C¹ provided (1) f is C¹ and (2) f is nonzero on the domain — leaves those two goals
  · apply ContDiffOn.sub                                    -- goal 1: 1 − ‖y‖² is C¹, as a difference of two C¹ functions
    · exact contDiffOn_const                                -- the constant 1 is C¹
    · exact (contDiff_norm_sq ℝ).contDiffOn                 -- ‖·‖² is C^∞ (hence C¹), restricted to the ball
  · intro x hx                                              -- goal 2: the radicand is nonzero; fix x in the ball
    rw [mem_ball_zero_iff] at hx                            -- turn x ∈ ball into the bound ‖x‖ < 1
    nlinarith [hx, norm_nonneg x]                           -- from 0 ≤ ‖x‖ < 1 get ‖x‖² < 1, so 1 − ‖x‖² > 0 (≠ 0)

noncomputable def rotationToNorthPole (h : n ≥ 1) (x₀ : EuclideanSpace ℝ (Fin n)) -- `h`: n ≥ 1 (last coord exists); `x₀`: the boundary point to move
    (hx₀ : x₀ ∈ unitSphere n) :                              -- assume ‖x₀‖ = 1, so x₀ and eₙ have equal length
    EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n) :=  -- output T: an affine isometry ℝⁿ ≃ ℝⁿ
  ((ℝ ∙ (x₀ - northPole h))ᗮ).reflection.toAffineIsometryEquiv  -- Householder reflection across the hyperplane ⊥ to u = x₀−eₙ (swaps x₀ ↔ eₙ), recast as ≃ᵃⁱ

/- Additional helper lemma for next proof-/

lemma norm_split (h : n ≥ 1) (x : EuclideanSpace ℝ (Fin n)) :
  ‖x‖^2 = ‖(WithLp.equiv 2 _).symm (fun i => x (dropLast h i))‖^2 + (x (lastIdx h))^2 := by  -- Pythagoras: ‖x‖² = ‖(first n−1 coords)‖² + (last coord)²
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩    -- write n = m+1 (legit since n ≥ 1) so `Fin n` genuinely has a last slot; substitutes everywhere
  simp_rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]  -- expand each ‖·‖ as √(∑ coords²), then square away the √ (sums of squares are ≥ 0)
  rw [Fin.sum_univ_castSucc]                                -- split ∑ over Fin (m+1) into (∑ over the first m, via castSucc) + (the last, m-th, term) — the actual Pythagorean step
  simp_rw [dropLast, lastIdx]                               -- unfold the index helpers so the first-m sum matches `dropLast` and the last term matches `lastIdx`
  simp only [Real.norm_eq_abs, sq_abs, Nat.add_one_sub_one, add_tsub_cancel_right]  -- normalize: |·|² = (·)², and simplify the index arithmetic (m+1)−1 = m so both sides align
  exact (add_left_inj (x.ofLp (Fin.last m) ^ 2)).mpr rfl    -- both sides share the last-coordinate term; cancel it and the remaining sums are definitionally equal


lemma sphere_eq_graph_near_northPole (h : n ≥ 1) :
    let U : Set (EuclideanSpace ℝ (Fin n)) := {x | x (lastIdx h) > 0}  -- work in the upper half-space U = {xₙ > 0}
    unitSphere n ∩ U = graphInRn h (heightFunction h) ∩ U := by  -- claim: on U, the sphere coincides with the graph of the height function
  ext x                                                     -- prove set equality pointwise
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, unitSphere, graphInRn, heightFunction, mem_sphere_zero_iff_norm]  -- unfold: sphere → ‖x‖=1, graph → xₙ = √(1−‖y‖²), U → xₙ > 0
  refine and_congr_left ?_                                  -- the U-conjunct (xₙ>0) is shared; reduce to proving the other conjuncts equivalent *given* xₙ > 0
  intro hxn                                                 -- assume hxn : 0 < xₙ
  constructor
  · intro hnorm                                             -- forward (on sphere ⇒ on graph): assume ‖x‖ = 1
    have hsq : ‖x‖^2 = 1 := by nlinarith                    -- square it: ‖x‖² = 1
    rw [norm_split h x] at hsq /- if only using have once, consolidate into one line-/  -- apply Pythagoras: ‖y‖² + xₙ² = 1
    have hrad : 1 - ‖(WithLp.equiv 2 _).symm (fun i => x (dropLast h i))‖^2 = (x (lastIdx h))^2 := by linarith  -- rearrange to: 1 − ‖y‖² = xₙ²
    rw [hrad, Real.sqrt_sq (le_of_lt hxn)]                  -- so √(1−‖y‖²) = √(xₙ²) = xₙ (as xₙ > 0), giving the graph equation
  · intro hsqrt                                             -- backward (on graph ⇒ on sphere): assume xₙ = √(1−‖y‖²)
    have hpos : 0 < 1 - ‖(WithLp.equiv 2 _).symm (fun i => x (dropLast h i))‖^2 := by  -- the radicand is strictly positive
      rw [hsqrt] at hxn                                     -- rewrite xₙ > 0 as √(1−‖y‖²) > 0
      exact Real.sqrt_pos.mp hxn                            -- √(·) > 0 ⇒ its argument > 0
    have hsq : ‖x‖^2 = 1 := by                              -- recover ‖x‖² = 1
      rw [norm_split h x, hsqrt, Real.sq_sqrt (le_of_lt hpos)]  -- Pythagoras + substitute xₙ = √(…) + (√r)² = r (since r > 0): ‖y‖² + (1−‖y‖²)
      ring                                                  -- … = 1
    nlinarith [norm_nonneg x, hsq]                          -- from ‖x‖² = 1 and ‖x‖ ≥ 0 conclude ‖x‖ = 1

lemma ball_eq_strictSubgraph_near_northPole (h : n ≥ 1) :
    let U : Set (EuclideanSpace ℝ (Fin n)) := {x | x (lastIdx h) > 0}  -- work in the upper half-space U = {xₙ > 0}
    unitBall n ∩ U =
      strictSubgraphInRn h (heightFunction h) ∩ U := by    -- claim: on U, the open ball coincides with the strict subgraph (points strictly below the graph)
  ext x                                                     -- prove set equality pointwise
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, unitBall, strictSubgraphInRn, heightFunction]  -- unfold: subgraph → xₙ < √(1−‖y‖²), U → xₙ > 0 (ball handled below via `mem_ball_zero_iff`)
  refine and_congr_left ?_                                  -- the U-conjunct (xₙ>0) is shared; reduce to the other conjuncts equivalent *given* xₙ > 0
  intro hxn                                                 -- assume hxn : 0 < xₙ
  constructor
  · intro hb                                                -- forward (in ball ⇒ in subgraph): assume x in the ball
    rw [mem_ball_zero_iff] at hb                            -- turn membership into ‖x‖ < 1
    rw [Real.lt_sqrt (le_of_lt hxn)]                        -- goal xₙ < √(1−‖y‖²); since xₙ ≥ 0, this is equivalent to xₙ² < 1−‖y‖²
    have hle : ‖x‖^2 < 1 := by nlinarith [norm_nonneg x, hb]  -- from ‖x‖ < 1 and ‖x‖ ≥ 0 get ‖x‖² < 1
    rw [norm_split h x] at hle                              -- Pythagoras: ‖y‖² + xₙ² < 1
    linarith                                                -- rearrange to xₙ² < 1 − ‖y‖²
  · intro hb                                                -- backward (in subgraph ⇒ in ball): assume xₙ < √(1−‖y‖²)
    rw [mem_ball_zero_iff]                                  -- goal becomes ‖x‖ < 1
    rw [Real.lt_sqrt (le_of_lt hxn)] at hb                  -- convert hb (using xₙ ≥ 0) to xₙ² < 1 − ‖y‖²
    nlinarith [norm_nonneg x, hb, norm_split h x]           -- combine with Pythagoras ‖x‖²=‖y‖²+xₙ² and ‖x‖ ≥ 0 to get ‖x‖ < 1

lemma northPole_mem_sphere (h : n ≥ 1) : northPole h ∈ unitSphere n := by  -- claim: the north pole eₙ lies on the unit sphere
  rw [unitSphere, mem_sphere_zero_iff_norm]                  -- unfold `unitSphere` and turn membership into the goal ‖eₙ‖ = 1
  show ‖EuclideanSpace.single (lastIdx h) (1 : ℝ)‖ = 1       -- rewrite eₙ to its definition: the basis vector with a 1 in the last slot
  rw [PiLp.norm_single]                                      -- norm of a one-hot vector = ‖its single entry‖ = ‖(1 : ℝ)‖
  norm_num                                                   -- ‖(1 : ℝ)‖ = 1, closing the goal

lemma rotationToNorthPole_apply (h : n ≥ 1) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : x₀ ∈ unitSphere n) :
    rotationToNorthPole h x₀ hx₀ x₀ = northPole h := by     -- claim: T sends x₀ to the north pole eₙ
  unfold rotationToNorthPole                                -- replace T by the underlying reflection
  set u : EuclideanSpace ℝ (Fin n) := x₀ - northPole h with hu  -- name the difference vector u = x₀ − eₙ (the reflection axis)
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ u)ᗮ with hK  -- name the reflecting hyperplane K = (line through u)ᗮ
  show K.reflection x₀ = northPole h                        -- goal in these names: reflecting x₀ across K yields eₙ
  have hx₀norm : ‖x₀‖ = 1 := by                             -- ‖x₀‖ = 1, since x₀ is on the sphere
    rw [unitSphere, mem_sphere_zero_iff_norm] at hx₀; exact hx₀
  have hnpnorm : ‖northPole h‖ = 1 := by                    -- ‖eₙ‖ = 1, via the earlier lemma that eₙ is on the sphere
    have := northPole_mem_sphere h
    rwa [unitSphere, mem_sphere_zero_iff_norm] at this
-- the midpoint of x₀ and eₙ
  set m : EuclideanSpace ℝ (Fin n) := (2⁻¹ : ℝ) • (x₀ + northPole h) with hm  -- m = ½(x₀ + eₙ)
  -- m ⊥ u, hence m ∈ K = (ℝ∙u)ᗮ
  have hmem_K : m ∈ K := by                                 -- show the midpoint lies in the fixed hyperplane
    rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_left, hm, hu]  -- reduce m ∈ K to the inner product ⟪m, u⟫ = 0
    rw [inner_smul_left, inner_sub_right, inner_add_left, inner_add_left]  -- expand ⟪½(x₀+eₙ), x₀−eₙ⟫ bilinearly
    simp only [real_inner_comm (northPole h) x₀]            -- identify the two cross terms ⟪x₀,eₙ⟫ = ⟪eₙ,x₀⟫ so they cancel
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx₀norm, hnpnorm]  -- ⟪x₀,x₀⟫=‖x₀‖²=1, ⟪eₙ,eₙ⟫=‖eₙ‖²=1
    ring_nf                                                 -- ½(1 − 1) = 0, closing the orthogonality goal
  -- ½u is on the line ℝ∙u
  have hmem_line : (2⁻¹ : ℝ) • u ∈ (ℝ ∙ u) :=               -- ½u is a scalar multiple of u, so it lies on the line ℝ∙u
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  -- x₀ = m + ½u
  have hdecomp : x₀ = m + (2⁻¹ : ℝ) • u := by               -- split x₀ into its hyperplane part m and its axis part ½u
    rw [hm, hu, smul_add, smul_sub]; module                 -- ½(x₀+eₙ) + ½(x₀−eₙ) = x₀, verified by `module`
  -- the line ℝ∙u equals Kᗮ
  have hline_eq : (ℝ ∙ u) = Kᗮ := by rw [hK, Submodule.orthogonal_orthogonal]  -- Kᗮ = (ℝ∙u)ᗮᗮ = ℝ∙u, so ½u ∈ Kᗮ
  -- reflect: K fixes m, negates ½u
  rw [hdecomp, map_add,                                      -- apply reflection to m + ½u; linearity splits it into the two pieces
      Submodule.reflection_mem_subspace_eq_self hmem_K,      -- reflection fixes m (it lies in K)
      Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg (hline_eq ▸ hmem_line)]  -- reflection negates ½u (it lies in Kᗮ)
  rw [hm, hu]; module                                        -- left with m − ½u = ½(x₀+eₙ) − ½(x₀−eₙ) = eₙ = northPole h

@[simp] lemma northPole_apply_last (h : n ≥ 1) :          -- @[simp]: register as a simp lemma; claim: the last coordinate of eₙ is 1
    (northPole h) (lastIdx h) = 1 := by
  simp [northPole, Pi.single_eq_same]                      -- unfold eₙ as the one-hot at `lastIdx h`; `Pi.single_eq_same` reads off its value there = 1


lemma rotationToNorthPole_apply_zero (h : n ≥ 1) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : x₀ ∈ unitSphere n) :
    rotationToNorthPole h x₀ hx₀ 0 = 0 := by               -- claim: T fixes the origin (it's a linear reflection, not an affine shift)
  unfold rotationToNorthPole                                -- replace T by the underlying reflection
  show ((ℝ ∙ (x₀ - northPole h))ᗮ).reflection 0 = 0         -- goal: that reflection sends 0 to 0
  exact map_zero _                                          -- immediate: the reflection is linear, and linear maps send 0 ↦ 0

lemma rotationToNorthPole_involutive (h : n ≥ 1) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : x₀ ∈ unitSphere n) (x : EuclideanSpace ℝ (Fin n)) :
    rotationToNorthPole h x₀ hx₀ (rotationToNorthPole h x₀ hx₀ x) = x := by  -- claim: T is an involution, so applying it twice is the identity (hence T⁻¹ = T)
  unfold rotationToNorthPole                                -- replace both copies of T by the underlying reflection
  show ((ℝ ∙ (x₀ - northPole h))ᗮ).reflection               -- goal: reflecting twice across the same hyperplane returns x
        (((ℝ ∙ (x₀ - northPole h))ᗮ).reflection x) = x
  exact Submodule.reflection_reflection _ x                 -- exactly Mathlib's fact that any subspace reflection is self-inverse




/-
-- THE MAIN THEOREM
theorem unitBall_hasC1Boundary (h : n ≥ 1) :
    HasC1Boundary h (unitBall n) := by                      -- goal: the open unit ball has a C¹ boundary
  intro x₀ hx₀                                              -- fix an arbitrary boundary point x₀ and the proof hx₀ that it's in ∂(ball)
  -- First: extract that x₀ is on the unit sphere
  rw [frontier_unitBall h] at hx₀                           -- since ∂(ball) = sphere, upgrade hx₀ to: x₀ ∈ unitSphere n
  -- Get our rotation T that maps x₀ to the north pole
  let T := rotationToNorthPole h x₀ hx₀                     -- the chart map: reflection sending x₀ ↦ eₙ

  -- Our open set V for the domain of g
  let V : Set (EuclideanSpace ℝ (Fin (n - 1))) := Metric.ball 0 1  -- domain of g: the open unit ball in ℝⁿ⁻¹

  -- Our graph function is the height function
  let g := heightFunction h                                 -- g(y) = √(1 − ‖y‖²): the upper hemisphere as a graph
  -- Our open set U: preimage under T of the upper half-space
  -- (i.e. points whose T-image has positive last coordinate)
  let U : Set (EuclideanSpace ℝ (Fin n)) :=                 -- U = the chart neighbourhood: pull the upper half-space {xₙ > 0} back through T
    T.symm '' {x | x (lastIdx h) > 0}                       -- (built via T.symm so that T '' U = {xₙ > 0} exactly)
  refine ⟨T, V, g, U, ?_, ?_, ?_, ?_, ?_, ?_⟩               -- supply the witnesses T, V, g, U; leaves the six conditions of `HasC1Boundary`
  · -- Condition 1: V is open ---------------------------------------------
    exact isOpen_ball                                       -- the open ball is open


  · -- Condition 2: g is C¹ on V ---------------------------------------------
    exact heightFunction_contDiffOn h                       -- the earlier lemma: the height function is C¹ on the ball


  · -- Condition 3: U is open ---------------------------------------------
    apply (T.symm.toHomeomorph).isOpenMap                   -- T.symm is a homeomorphism ⇒ open map, so it suffices that the half-space is open
    exact isOpen_lt continuous_const (by fun_prop)          -- {x | 0 < x(lastIdx)} is open: locus where a constant < a continuous coordinate map
    -- T.symm is continuous and {xₙ > 0} is open, so preimage is open


  · -- Condition 4: x₀ ∈ U ---------------------------------------------
    refine ⟨T x₀, ?_, T.symm_apply_apply x₀⟩                -- to put x₀ in T.symm '' {xₙ>0}, use witness T x₀; T.symm(T x₀)=x₀ is automatic, leaving T x₀ ∈ {xₙ>0}
    show (T x₀) (lastIdx h) > 0                              -- remaining goal: the last coordinate of T x₀ is positive
    rw [show T x₀ = northPole h from rotationToNorthPole_apply h x₀ hx₀,  -- T x₀ = eₙ (key property of T) …
        northPole_apply_last]                               -- … and eₙ's last coordinate is 1
    norm_num                                                -- 1 > 0
    -- T(x₀) = northPole = eₙ, and eₙ has last coordinate = 1 > 0
    -- so x₀ = T.symm(eₙ) ∈ T.symm '' {xₙ > 0}



  · -- Condition 5: frontier(ball) ∩ U = T '' graph ∩ U ---------------------------------------------
    rw [frontier_unitBall h]                                -- rewrite ∂(ball) = sphere, so the goal is about unitSphere n
    -- T preserves norms (it's a linear reflection underneath), hence the sphere
    have hnorm : ∀ z, ‖T z‖ = ‖z‖ := by                     -- T is a linear isometry, so it preserves norms
      intro z
      show ‖((ℝ ∙ (x₀ - northPole h))ᗮ).reflection z‖ = ‖z‖ -- unfold T to its underlying reflection
      exact LinearIsometryEquiv.norm_map _ z                -- reflections are isometries: ‖reflect z‖ = ‖z‖
    have hsphere : T '' unitSphere n = unitSphere n := by   -- norm preservation ⇒ T maps the sphere onto itself
      ext y
      simp only [unitSphere, Set.mem_image, mem_sphere_zero_iff_norm]  -- both sides reduce to statements about ‖·‖ = 1
      constructor
      · rintro ⟨z, hz, rfl⟩; rw [hnorm]; exact hz           -- forward: if ‖z‖=1 then ‖T z‖=‖z‖=1
      · intro hy                                            -- backward: given ‖y‖=1, exhibit T.symm y as a preimage
        exact ⟨T.symm y, by rw [← hnorm (T.symm y), T.apply_symm_apply]; exact hy,
          T.apply_symm_apply y⟩
    -- T '' U = the un-rotated half-space (T ∘ T.symm = id)
    have hTU : T '' U = {x | x (lastIdx h) > 0} := by       -- pushing U back through T recovers the half-space (by construction of U)
      show T '' (T.symm '' {x | x (lastIdx h) > 0}) = {x | x (lastIdx h) > 0}
      rw [Set.image_image]                                  -- compose the two images into x ↦ T (T.symm x)
      have : (fun x => T (T.symm x)) = (id : EuclideanSpace ℝ (Fin n) → _) := by
        funext x; exact T.apply_symm_apply x                -- T ∘ T.symm = id
      rw [this, Set.image_id]                               -- so the double image is the identity image
    -- T '' (T '' graph) = graph (T is an involution)
    have hTTG : T '' (T '' graphInRn h g) = graphInRn h g := by  -- applying T twice to the graph returns the graph
      rw [Set.image_image]                                  -- compose into x ↦ T (T x)
      have : (fun x => T (T x)) = (id : EuclideanSpace ℝ (Fin n) → _) := by
        funext x; exact rotationToNorthPole_involutive h x₀ hx₀ x  -- T ∘ T = id (T is an involution)
      rw [this, Set.image_id]
    -- push T through and reduce to the local lemma
    rw [← Set.image_eq_image T.injective, Set.image_inter T.injective,  -- apply T '' to both sides (T injective) and distribute over ∩
        Set.image_inter T.injective, hsphere, hTTG]         -- simplify T '' sphere = sphere and T '' (T '' graph) = graph
    simp only [hTU]                                         -- replace the leftover T '' U by {xₙ > 0}
    exact sphere_eq_graph_near_northPole h                  -- now exactly the local lemma: sphere ∩ {xₙ>0} = graph ∩ {xₙ>0}
    -- Use frontier_unitBall and sphere_eq_graph_near_northPole
    -- plus the fact that T is a bijection to move between the two sides



  · -- Condition 6: ball ∩ U = T '' strictSubgraph ∩ U ---------------------------------------------
    have hnorm : ∀ z, ‖T z‖ = ‖z‖ := by                     -- (same norm-preservation fact as in Condition 5)
      intro z
      show ‖((ℝ ∙ (x₀ - northPole h))ᗮ).reflection z‖ = ‖z‖
      exact LinearIsometryEquiv.norm_map _ z
    have hball : T '' unitBall n = unitBall n := by         -- norm preservation ⇒ T maps the open ball onto itself
      ext y
      simp only [unitBall, Set.mem_image, mem_ball_zero_iff]  -- both sides reduce to ‖·‖ < 1
      constructor
      · rintro ⟨z, hz, rfl⟩; rw [hnorm]; exact hz           -- forward: ‖z‖<1 ⇒ ‖T z‖<1
      · intro hy                                            -- backward: T.symm y is a preimage with ‖T.symm y‖ = ‖y‖ < 1
        exact ⟨T.symm y, by rw [← hnorm (T.symm y), T.apply_symm_apply]; exact hy,
          T.apply_symm_apply y⟩
    have hTU : T '' U = {x | x (lastIdx h) > 0} := by       -- (same as Condition 5: T '' U = half-space)
      show T '' (T.symm '' {x | x (lastIdx h) > 0}) = {x | x (lastIdx h) > 0}
      rw [Set.image_image]
      have : (fun x => T (T.symm x)) = (id : EuclideanSpace ℝ (Fin n) → _) := by
        funext x; exact T.apply_symm_apply x
      rw [this, Set.image_id]
    have hTTS : T '' (T '' strictSubgraphInRn h g) = strictSubgraphInRn h g := by  -- T involution ⇒ double image of the subgraph is itself
      rw [Set.image_image]
      have : (fun x => T (T x)) = (id : EuclideanSpace ℝ (Fin n) → _) := by
        funext x; exact rotationToNorthPole_involutive h x₀ hx₀ x
      rw [this, Set.image_id]
    rw [← Set.image_eq_image T.injective, Set.image_inter T.injective,  -- apply T '' to both sides and distribute over ∩, as before
        Set.image_inter T.injective, hball, hTTS]           -- simplify T '' ball = ball and T '' (T '' subgraph) = subgraph
    simp only [hTU]                                         -- replace leftover T '' U by {xₙ > 0}
    exact ball_eq_strictSubgraph_near_northPole h           -- now exactly the local lemma: ball ∩ {xₙ>0} = subgraph ∩ {xₙ>0}
    -- Use ball_eq_strictSubgraph_near_northPole similarly
-/

theorem unitBall_hasC1Boundary (h : n ≥ 1) :
    HasC1Boundary h (unitBall n) := by
  intro x₀ hx₀
  -- since ∂(ball) = sphere, x₀ lies on the unit sphere
  rw [frontier_unitBall h] at hx₀
  -- the chart map: the reflection sending x₀ ↦ eₙ
  -- it is an involution, so T '' s = T ⁻¹' s
  let T := rotationToNorthPole h x₀ hx₀
  have hT : Function.Involutive T := rotationToNorthPole_involutive h x₀ hx₀
  -- T is a linear isometry, so it preserves norms
  have hnorm (z) : ‖T z‖ = ‖z‖ := ((ℝ ∙ (x₀ - northPole h))ᗮ).reflection.norm_map z
  -- V is the unit ball of ℝⁿ⁻¹, g the height function, U the pullback of {xₙ > 0} under T
  refine ⟨T, Metric.ball 0 1, heightFunction h, T ⁻¹' {x | x (lastIdx h) > 0}, isOpen_ball,
    heightFunction_contDiffOn h, (isOpen_lt continuous_const (by fun_prop)).preimage T.continuous,
    ?_, ?_, ?_⟩
  · -- T x₀ = eₙ, whose last coordinate is 1 > 0
    simp [T, rotationToNorthPole_apply]
  · -- T preserves the sphere, so this is the local lemma near the north pole pulled back by T
    rw [frontier_unitBall h, hT.image_eq_preimage_symm, ← Set.preimage_inter,
      ← sphere_eq_graph_near_northPole h]
    ext; simp [unitSphere, hnorm]
  · -- T preserves the ball, so this is the local lemma near the north pole pulled back by T
    rw [hT.image_eq_preimage_symm, ← Set.preimage_inter,
      ← ball_eq_strictSubgraph_near_northPole h]
    ext; simp [unitBall, hnorm]
