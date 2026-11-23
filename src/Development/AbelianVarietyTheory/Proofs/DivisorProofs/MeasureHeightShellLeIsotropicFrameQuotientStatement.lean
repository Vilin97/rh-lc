module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizerStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalPropertiesStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import GroundTheory.AutomorphicForms.QuotientMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompact

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem slab_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D b hb
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) :=
    (HtCont.isCompact_isHt_scales F E σ n J r X Y L a h D).1
  refine ⟨(fun q : ℝ × GAd σ J => b q.1 * q.2) '' (Set.Icc (-1 : ℝ) 0 ×ˢ (levelAll σ J L a : Set (GAd σ J))), ?_, ?_⟩
  · exact (isCompact_Icc.prod hK).image ((hb.cont.comp continuous_fst).mul continuous_snd)
  · intro g h1 h2
    obtain ⟨p, l, hp, k, hk, rfl⟩ := D.iwa g
    rw [D.ht p l hp k hk] at h1 h2
    have hpos : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det l) := lt_of_lt_of_le (Real.exp_pos _) h1
    set t : ℝ := Real.log (absE F E (Matrix.GeneralLinearGroup.det l)) with ht
    have ht1 : -1 ≤ t := (Real.le_log_iff_exp_le hpos).2 h1
    have ht0 : t ≤ 0 := Real.log_nonpos hpos.le h2
    obtain ⟨l', hl', hal'⟩ := hb.onX (-t)
    have hs : ScalesBy σ J X (p * b (-t)) (l * l') := by
      unfold ScalesBy at *
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hl', ← Matrix.mul_assoc, hp, Matrix.mul_assoc, Units.val_mul]
    have hone : absE F E (Matrix.GeneralLinearGroup.det (l * l')) = 1 := by
      apply NNReal.coe_injective
      rw [map_mul, map_mul, NNReal.coe_mul, hal', Real.exp_neg, ht, Real.exp_log hpos, mul_inv_cancel₀ hpos.ne', NNReal.coe_one]
    obtain ⟨u, hu, m, -, e, -, -, hm⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y D.cm D.herm D.witt _ _ hs
    have h0 : b 0 = 1 := by
      have := hb.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    refine ⟨u, hu, m, hm hone, b t * k, ⟨(t, k), ⟨⟨ht1, ht0⟩, hk⟩, rfl⟩, ?_⟩
    rw [← e, mul_assoc, ← mul_assoc (b (-t)), ← hb.add, neg_add_cancel, h0, one_mul]

end GlobalTheory.ResidueEisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompactStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.heightSlab_subset_unipotent_levi_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  first | exact @GlobalTheory.ResidueEisenstein.slab_subset | exact GlobalTheory.ResidueEisenstein.slab_subset | (intros; apply GlobalTheory.ResidueEisenstein.slab_subset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotentStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | exact GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOneStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  first | exact @GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | exact GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | (intros; apply GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLattice

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem inf_subgroupOf_of_le' {G : Type} [Group G] {Γ P H : Subgroup G} (h : H ≤ P) :
    (Γ ⊓ P).subgroupOf H = Γ.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩

theorem semiLat_frameGrp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 →
      ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})),
        SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤)
          ν π DN DM := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW ν DN hν hDN h1
  obtain ⟨π, DM, hπ, hDM⟩ := GlobalTheory.StdPar.exists_haar_leviOne (X := X) (Y := Y) {Fin.last r} h hJ hW
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y h hJ hW
  have hN : unipRad σ J X ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun u hu => ⟨1, trivial, f3 u hu⟩
  have hM : GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun m hm => by
    obtain ⟨β, e, -⟩ := f4 m hm
    exact ⟨β, trivial, e⟩
  refine ⟨π, DM,
    { closedN := (GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one F E σ n J r X Y h hJ hW).1
      closedM := f7
      norm := fun m hm => f1 m (f6 hm)
      disj := fun g hg hg' => f2 g hg (f6 hg')
      dec := ?_
      haarN := hν
      haarM := hπ
      domN := by rw [inf_subgroupOf_of_le' hN]; exact hDN
      domM := by rw [inf_subgroupOf_of_le' hM]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer F E σ n J r X Y h hJ hW π DM hπ hDM }⟩
  rintro γ ⟨hγ, β, -, e⟩
  obtain ⟨u, hu, m, -, hp, -, hr, ho⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y h hJ hW γ β e
  have hm := ho (f5 γ hγ β e)
  refine ⟨u, hu, m, hm, ⟨?_, hN hu⟩, ⟨hr hγ, hM hm⟩, hp⟩
  have : u = γ * m⁻¹ := by rw [hp, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.ResidueEisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLatticeStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.rational_isotropicStabiliser_splitLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 → ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) ν π DN DM := by
  first | exact @GlobalTheory.ResidueEisenstein.semiLat_frameGrp | exact GlobalTheory.ResidueEisenstein.semiLat_frameGrp | (intros; apply GlobalTheory.ResidueEisenstein.semiLat_frameGrp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotient

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem measure_shell_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD μ D hμ hFD
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_leviCentreFlow_wittFrame F E σ n J r X Y hD.cm hD.herm hD.witt
  obtain ⟨-, hHt, hlaw⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame F E σ n J r X Y L a h hD
  obtain ⟨-, ν, DN, hν, hDN, hone⟩ := unipRad_frame_closed_mass_one F E σ n J r X Y hD.cm hD.herm hD.witt
  have hmod := GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent F E σ n J r X Y hD.cm hD.herm hD.witt b hb ν hν
  obtain ⟨π, DM, hSL⟩ := GlobalTheory.T.rational_isotropicStabiliser_splitLattice F E σ n J r X Y hD.cm hD.herm hD.witt ν DN hν hDN hone
  obtain ⟨C, hC, hslab⟩ := GlobalTheory.T.heightSlab_subset_unipotent_levi_compact F E σ n J r X Y L a h hD b hb
  haveI : Countable (ratPts σ J) := inferInstance
  haveI : Countable ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) :=
    Function.Injective.countable (Subgroup.inclusion_injective
      (inf_le_left : ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤ ≤ ratPts σ J))
  obtain ⟨B, hB, hsh⟩ := GlobalTheory.ResLine.modulus_mul_measure_shell_le (GAd σ J) _ _ _ ν π DN DM hSL μ D hμ hFD C hC
  refine ⟨B, hB, fun j => ?_⟩
  have hS : MeasurableSet {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} :=
    (measurableSet_Ioc (a := Real.exp (-(j + 1 : ℝ))) (b := Real.exp (-(j : ℝ)))).preimage hHt.cont.measurable
  have key := hsh (b j) _ (fun m hm => hb.comm j m (Subgroup.mem_inf.mp hm).1) (hmod j) _ hS (fun x hx => by
    obtain ⟨β, hβ, e⟩ := hb.onX j
    have e2 : h (b j * x) = Real.exp j * h x := by rw [hlaw _ β hβ, e]
    have hp : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    refine hslab _ ?_ ?_
    · rw [e2]
      have : Real.exp (-1) = Real.exp j * Real.exp (-(j + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.1.le hp.le
    · rw [e2]
      have : (1 : ℝ) = Real.exp j * Real.exp (-(j : ℝ)) := by rw [← Real.exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.2 hp.le)
  rw [Measure.restrict_apply hS]
  have e1 : ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc _ = ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * (ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) * _) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * B := by gcongr
    _ = _ := mul_comm _ _

end GlobalTheory.ResidueEisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotientStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.measure_heightShell_le_isotropicFrame_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  first | exact @GlobalTheory.ResidueEisenstein.measure_shell_le | exact GlobalTheory.ResidueEisenstein.measure_shell_le | (intros; apply GlobalTheory.ResidueEisenstein.measure_shell_le <;> assumption)
end
end
