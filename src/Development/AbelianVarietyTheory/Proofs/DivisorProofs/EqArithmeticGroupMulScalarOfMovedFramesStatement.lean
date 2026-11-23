module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelGamS

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_gl_mul (τ : E →+* ℂ) (γ₁ γ₂ : GL (Fin r) E) :
    ((γ₁ * γ₂ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ =
      (γ₁ : Matrix (Fin r) (Fin r) E).map τ * (γ₂ : Matrix (Fin r) (Fin r) E).map τ := by
  rw [Units.val_mul, Matrix.map_mul]

theorem map_gl_inv_mul (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (γ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← map_gl_mul, inv_mul_cancel, Units.val_one, Matrix.map_one]
  all_goals first | exact τ.map_zero | exact τ.map_one

def TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, ∀ a c : Fin r, c < a → (adjugate (mat x τ) * g.map τ.1 * mat x τ) a c = 0}

theorem isClosed_TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : IsClosed (TSet Ψ g) := by
  simp only [TSet, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
    isClosed_iInter fun _ => ?_
  have hm : Continuous fun x : Frame Ψ r => mat x τ :=
    continuous_pi fun i => continuous_pi fun j => by
      simp only [mat, Matrix.of_apply]
      fun_prop
  exact isClosed_eq
    (((hm.matrix_adjugate.matrix_mul continuous_const).matrix_mul hm).matrix_elem a c)
    continuous_const

theorem mem_TSet (Ψ : Finset (E →+* ℂ)) (γ γ' : GL (Fin r) E) {x b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (h : lact γ x = rmul (lact γ' x) b) : x ∈ TSet Ψ ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
  change ∀ τ : Ψ, ∀ a c : Fin r, c < a →
    (adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) a c = 0
  intro τ a c hca
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) := by
    have h0 := congrArg (fun y => mat y τ) h
    rw [← Matrix.mul_assoc]
    exact h0
  have h2 : adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat x τ = (mat x τ).det • mat b τ := by
    rw [map_gl_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc _ ((γ' : Matrix (Fin r) (Fin r) E).map τ.1), map_gl_inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h2, Matrix.smul_apply, smul_eq_mul]
  have hB : b τ a c = 0 := (hb τ).2 a c hca
  simp [mat, hB]

theorem scalar_step {Ψ : Finset (E →+* ℂ)} (τ₀ : Ψ) (g : Matrix (Fin r) (Fin r) E) {W : Set (Frame Ψ r)}
    (hWo : IsOpen W) (hWT : W ⊆ TSet Ψ g) {y : Frame Ψ r} (hyW : y ∈ W) (hy : (mat y τ₀).det ≠ 0) :
    ∃ κ : ℂ, g.map τ₀.1 = κ • 1 := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, by ext a; exact Fin.elim0 a⟩
  set M : Matrix (Fin r) (Fin r) ℂ := g.map τ₀.1 with hM
  let i0 : Fin r := ⟨0, hr⟩
  let fr : (Fin r → ℂ) → Frame Ψ r := fun v τ a c => if τ = τ₀ ∧ c = i0 then v a else y τ a c
  let v₀ : Fin r → ℂ := fun a => y τ₀ a i0
  have hfr : Continuous fr := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    by_cases h : τ = τ₀ ∧ c = i0
    · simp only [fr, if_pos h]
      exact continuous_apply a
    · simp only [fr, if_neg h]
      exact continuous_const
  have hfr0 : fr v₀ = y := by
    funext τ a c
    by_cases h : τ = τ₀ ∧ c = i0
    · obtain ⟨rfl, rfl⟩ := h
      simp [fr, v₀]
    · simp [fr, h]
  have hdet : Continuous fun v => (mat (fr v) τ₀).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun c => by
      simp only [mat, Matrix.of_apply]
      exact (continuous_apply c).comp ((continuous_apply a).comp ((continuous_apply τ₀).comp hfr))
  have hW1 : ∀ᶠ v in nhds v₀, fr v ∈ W := (hfr.tendsto' v₀ y hfr0) (hWo.mem_nhds hyW)
  have hP : ∀ᶠ v in nhds v₀, fr v ∈ W ∧ (mat (fr v) τ₀).det ≠ 0 :=
    hW1.and (hdet.continuousAt.eventually_ne (by
      show (mat (fr v₀) τ₀).det ≠ 0
      rw [hfr0]
      exact hy))
  have hB : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 → ∃ l : ℂ, M *ᵥ v = l • v := by
    intro v hvW hd
    have hT : ∀ τ : Ψ, ∀ a c : Fin r, c < a →
        (adjugate (mat (fr v) τ) * g.map τ.1 * mat (fr v) τ) a c = 0 := hWT hvW
    set X := mat (fr v) τ₀ with hX
    have hcol : ∀ a, X a i0 = v a := fun a => by simp [hX, mat, fr]
    set z := X.adjugate *ᵥ (M *ᵥ v) with hz
    have hz0 : ∀ a, a ≠ i0 → z a = 0 := by
      intro a ha
      have h1 := hT τ₀ a i0 (by
        rw [Fin.lt_iff_val_lt_val]
        exact Nat.pos_of_ne_zero fun h => ha (Fin.ext h))
      have h2 : z a = (X.adjugate * M * X) a i0 := by
        rw [hz, Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hcol]
      rw [h2]
      exact h1
    have hXz : X *ᵥ z = X.det • (M *ᵥ v) := by
      calc X *ᵥ z = (X * X.adjugate) *ᵥ (M *ᵥ v) := by
            rw [hz]
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = X.det • (M *ᵥ v) := by
            rw [Matrix.mul_adjugate]
            first
              | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
              | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    have hXz' : X *ᵥ z = z i0 • v := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hz0 b hb, mul_zero])
        (fun h => absurd (Finset.mem_univ i0) h), hcol, mul_comm]
    refine ⟨z i0 / X.det, ?_⟩
    funext a
    have ha := congrFun (hXz.symm.trans hXz') a
    simp only [Pi.smul_apply, smul_eq_mul] at ha ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination ha
  have hQ : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 →
      ∀ a b, (M *ᵥ v) a * v b = (M *ᵥ v) b * v a := by
    intro v h1 h2 a b
    obtain ⟨l, hl⟩ := hB v h1 h2
    rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hall : ∀ u : Fin r → ℂ, ∀ a b, (M *ᵥ u) a * u b = (M *ᵥ u) b * u a := by
    intro u a b
    have t1 : Filter.Tendsto (fun s : ℂ => v₀ + s • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have t2 : Filter.Tendsto (fun s : ℂ => v₀ + (2 * s) • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have e1 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, fr (v₀ + s • u) ∈ W ∧ (mat (fr (v₀ + s • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t1.eventually hP)
    have e2 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ,
        fr (v₀ + (2 * s) • u) ∈ W ∧ (mat (fr (v₀ + (2 * s) • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t2.eventually hP)
    have e3 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, s ≠ 0 := self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2, hs0⟩ := (e1.and (e2.and e3)).exists
    have q0 := hQ v₀ (by rw [hfr0]; exact hyW) (by rw [hfr0]; exact hy) a b
    have q1 := hQ _ hs1.1 hs1.2 a b
    have q2 := hQ _ hs2.1 hs2.2 a b
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at q1 q2
    have key : (2 * s ^ 2) * ((M *ᵥ u) a * u b - (M *ᵥ u) b * u a) = 0 := by
      linear_combination q2 - 2 * q1 + q0
    have hs2' : (2 * s ^ 2 : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs2')
  have hcolv : ∀ j i, (M *ᵥ Pi.single j 1) i = M i j := by
    intro j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hoff : ∀ a b, a ≠ b → M a b = 0 := by
    intro a b hab
    have h := hall (Pi.single b 1) a b
    rw [hcolv, hcolv] at h
    simpa [Pi.single_apply, hab] using h
  have hdiag : ∀ a b, M a a = M b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have h := hall (Pi.single a 1 + Pi.single b 1) a b
    rw [Matrix.mulVec_add] at h
    simp only [Pi.add_apply, hcolv] at h
    simp [Pi.single_apply, hab, Ne.symm hab, hoff a b hab, hoff b a (Ne.symm hab)] at h
    linear_combination h
  refine ⟨M i0 i0, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag a i0]
  · simp [hoff a b hab, hab]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFrames

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem orbit_open_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (τ₀ : Ψ) (G : Subgroup (GL (Fin r) E)) (h : GL (Fin r) E) {O : Set (Frame Ψ r)} (hO : IsOpen O)
    (hne : O.Nonempty) (hdet : ∀ y ∈ O, (mat y τ₀).det ≠ 0)
    (H1 : ∀ y ∈ O, ∃ γ ∈ G, ∃ b ∈ Bor Ψ r, lact h y = rmul (lact γ y) b) :
    ∃ γ ∈ G, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hy₀
  set B₀ := Metric.ball y₀ ρ with hB₀
  let f : Option G → Set (Frame Ψ r) := fun o => match o with
    | none => B₀ᶜ
    | some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | γ')
    · exact Metric.isOpen_ball.isClosed_compl
    · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ B₀
    · obtain ⟨γ', hγ', b, hb, e⟩ := H1 x (hball hx)
      exact ⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩
    · exact ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyB, hyU⟩ := hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hyU
  cases o with
  | none => exact absurd hyB (interior_subset ho)
  | some γ' =>
    set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg
    obtain ⟨κ, hκ⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g
      (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball)
      (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))
    have hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0 := by
      intro a b
      have := congrFun (congrFun hκ a) b
      simpa [Matrix.one_apply] using this
    have hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g := by
      rw [hg, ← Units.val_mul, mul_inv_cancel_left]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact ⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩
    · refine ⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
      rw [hh]
      congr 1
      ext a b
      apply τ₀.1.injective
      rw [hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, hent, if_pos rfl]
      · rw [if_neg hab, if_neg hab, map_zero]

theorem eq_mul_scalar_of_moved {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E) (hΨ : X₂.Ψ = X.Ψ)
    (H : ∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) :
    ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical

  obtain ⟨τ₁⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases hτ : τ₁ ∈ X.Ψ
    · exact ⟨τ₁, hτ⟩
    · refine ⟨ComplexEmbedding.conjugate τ₁, ?_⟩
      by_contra hc
      exact hτ ((X.cmType τ₁).2 hc)
  have hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ := fun τ => hΨ ▸ τ.2
  have hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ := fun τ => hΨ.symm ▸ τ.2

  let back : Frame X.Ψ r → Frame X₂.Ψ r := fun y τ =>
    (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  let fwd : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hback : Continuous back := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩ := continuous_apply _
    exact (continuous_const.matrix_mul hm).matrix_elem a b
  have hbf : ∀ x, back (fwd x) = x := by
    intro x
    funext τ
    show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]
  have hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y := by
    intro y τ h₂ h₁
    show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)
    rw [← Matrix.mul_assoc]
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]
  have hdom : (X₂.dom).Nonempty := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩
  obtain ⟨x₀, hx₀⟩ := hdom
  refine orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom)
    ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_
    (fun y hy => H _ hy y (hmoved y))
  intro y hy
  have h1 := (hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1
  have h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩ := rfl
  rw [h2, Matrix.det_mul] at h1
  exact right_ne_zero_of_mul h1

end GlobalTheory.LevModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFramesStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E), X₂.Ψ = X.Ψ → (∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) → ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  first | exact @GlobalTheory.LevModel.eq_mul_scalar_of_moved | exact GlobalTheory.LevModel.eq_mul_scalar_of_moved | (intros; apply GlobalTheory.LevModel.eq_mul_scalar_of_moved <;> assumption)
end
end
