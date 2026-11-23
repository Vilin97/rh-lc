module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Blocks
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.EntryEqZeroOfComm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.RelOpCurve
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Stable
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepHom
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Decomp

section

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem finrank_eq_sum_of_orth {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {m : ℕ} (A : Fin m → Submodule ℂ V)
    (horth : ∀ i i', i ≠ i' → ∀ y ∈ A i, ∀ z ∈ A i', ⟪y, z⟫_ℂ = 0) (htop : (⨆ i, A i) = ⊤) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (A i) := by
  classical
  have hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ :=
    fun i j hij v w => horth i j hij _ v.2 _ w.2
  have hind : iSupIndep A := by
    first
      | exact hOF.independent
      | exact hOF.iSupIndep
  have hint : DirectSum.IsInternal A := by
    first
      | exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩
      | exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)),
    Fintype.card_sigma]
  simp

theorem compRed_of (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by
  intro n ε R
  obtain ⟨hrel, hunit⟩ := hR n ε R
  obtain ⟨m, x, μ, hx, horth, htop⟩ :=
    Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)
  refine ⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩
  · exact finrank_eq_sum_of_orth _ horth htop
  · intro i k v hv
    exact (hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv
  · intro i
    obtain ⟨T, φ, h1, h2, h3⟩ := hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2
    exact ⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivK

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma onepCurve_zero (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    onepCurve ε hX 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp [onepCurve]

lemma hasDerivAt_mul_of_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : ℝ → A} {a b : A}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    HasDerivAt (fun t => f t * g t) (a + b) 0 := by
  have h := hf.mul hg
  rw [hf0, hg0, one_mul, mul_one] at h
  exact h

theorem derivExists_of_split (h : DerivExistsAllPosStatement) (ε : Fin n → Bool)
    (p : Bool → ℕ) (emb : ∀ s, KG (fun _ : Fin (p s) => true) →* KG ε)
    (hemb : ∀ s, Continuous (emb s))
    (blk : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (p s)) (Fin (p s)) ℂ)
    (hblk : ∀ s X, inK ε X → inK (fun _ : Fin (p s) => true) (blk s X))
    (hsplit : ∀ X (hX : inK ε X) (t : ℝ),
      toMK (emb true (onepCurve _ (hblk true X hX) t)) *
          toMK (emb false (onepCurve _ (hblk false X hX) t)) =
        NormedSpace.exp ((t : ℂ) • X))
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0 := by
  choose dτs hdτs using fun s => h (p s) V (τ.comp (emb s)) (hτ.comp (hemb s))
  refine ⟨(dτs true).comp (blk true) + (dτs false).comp (blk false), fun X hX γ hγ => ?_⟩
  have hγeq : ∀ t, γ t = emb true (onepCurve _ (hblk true X hX) t) *
      emb false (onepCurve _ (hblk false X hX) t) := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (hγ t).trans (hsplit X hX t).symm
  have hd1 := hdτs true (blk true X) (hblk true X hX) (onepCurve _ (hblk true X hX))
    (toMK_onepCurve _ (hblk true X hX))
  have hd2 := hdτs false (blk false X) (hblk false X hX) (onepCurve _ (hblk false X hX))
    (toMK_onepCurve _ (hblk false X hX))
  have hprod := hasDerivAt_mul_of_one hd1 hd2 (by simp [onepCurve_zero]) (by simp [onepCurve_zero])
  have hfun : (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      fun t => (((τ.comp (emb true)) (onepCurve _ (hblk true X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) *
        (((τ.comp (emb false)) (onepCurve _ (hblk false X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
    funext t
    rw [hγeq t, map_mul]
    rfl
  rw [hfun]
  simpa using hprod

theorem derivExists_of (h : DerivExistsAllPosStatement) : DerivExistsStatement := by
  intro n ε V _ _ _ τ hτ
  refine derivExists_of_split h ε (blkP ε) (blkEmbed ε) (continuous_blkEmbed ε) (blkRes ε)
    (fun s X hX => inK_blkRes hX s) (fun X hX t => ?_) V τ hτ
  have hc := blk_curve hX (onepCurve ε hX) (toMK_onepCurve ε hX)
    (onepCurve _ (inK_blkRes hX true)) (toMK_onepCurve _ (inK_blkRes hX true))
    (onepCurve _ (inK_blkRes hX false)) (toMK_onepCurve _ (inK_blkRes hX false)) t
  have h1 := congrArg toMK hc
  rw [toMK_onepCurve] at h1
  exact h1.symm

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRedOf

section

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma inUJ_of_mem_K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  simp only [Kset, inUJ, Set.mem_setOf_eq] at *
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]

def cr2K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_K ε hg⟩, hg⟩

lemma KRep.actM_units {ε : Fin n → Bool} (R : KRep ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : R.V) :
    actM R.units X v = R.dτ X v := by
  simp only [KRep.units, actM]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  have h : ∀ a b, Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
    intro a b; rw [Matrix.smul_single, smul_eq_mul, mul_one]

  simp only [h, map_sum, map_smul]
  simp [LinearMap.sum_apply, ContinuousLinearMap.sum_apply]

def compactRepOfUnitaryDifferential (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (τ : KG ε →* unitary (H →L[ℂ] H)) (hτ : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
      (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0) : KRep ε :=
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  { V := H, τ := τ, cont := hτ, dτ := dτ, hasDeriv := hd }

theorem uRepCompRed_of (hU : URepHomStatement) (hD : DerivExistsStatement)
    (hR : KRepRelStatement) (hC : CompRedStatement) : URepCompRedStatement := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨τ, hτc, hτ⟩ := hU n ε H σ hσ
  obtain ⟨dτ, hd⟩ := hD n ε H τ hτc
  obtain ⟨hRel, hUnit⟩ := hR n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  obtain ⟨m, x, μ, h1, h2, h3, h4, h5, h6⟩ := hC n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  refine ⟨(compactRepOfUnitaryDifferential ε H τ hτc dτ hd).units, hRel, hUnit, ?_, m, x, μ, h1, h2, h3, ?_⟩
  · intro X hX v
    have hK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t =>
      (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (Formalism.REAL.inK_smul_real ε hX t)
    have hγ : ∀ t : ℝ, toMK (cr2K ε (hK t)) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hder := hd X hX (fun t => cr2K ε (hK t)) hγ
    erw [KRep.actM_units (compactRepOfUnitaryDifferential ε H τ hτc dτ hd) X v]
    have hfun : (fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • X))) v) =
        fun t : ℝ => (((τ (cr2K ε (hK t)) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) v := by
      funext t; rw [hτ, hγ]
    rw [hfun]
    have h2 := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
    exact h2
  · refine ⟨?_, ?_⟩
    · intro i g hg v hv
      have := h5 i (cr2K ε hg) v hv
      simp only [KRep.op, compactRepOfUnitaryDifferential] at this
      have e : σ g = ((τ (cr2K ε hg) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
        rw [hτ]; rfl
      rw [e]; exact this
    · intro i
      obtain ⟨T, φ, -, hop, hdτ, hw⟩ := h6 i
      refine ⟨T, φ, ?_, ?_, hw⟩
      · intro k v
        have e : σ (toMK k) = ((τ k : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := (hτ k).symm
        rw [e]; exact hop k v
      · intro a b hab v
        have hc : Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
          show Matrix.single a b (1 : ℂ) * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.single a b 1
          ext i j
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
          by_cases h : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := h; simp [hab]
          · simp [h]
        exact hdτ _ hc v

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem kRepPiece : KRepPieceStatement := kRepPiece_of kRepRel kRepStable

theorem compRed : CompRedStatement := compRed_of kRepRel kRepStable kRepPiece

theorem derivExists : DerivExistsStatement := derivExists_of derivExists_allPos

theorem uRepCompRed : URepCompRedStatement := uRepCompRed_of uRepHom derivExists kRepRel compRed

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
