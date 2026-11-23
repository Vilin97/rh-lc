module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffPoincareSumOverRationalHomRealDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinatePoincareSumHalfWittEqBumpStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCoreStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBump

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMix

theorem finite_rat_mem_of_isCompact {D : D7} {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, -, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := hg
  haveI : T2Space (Mx D m n) := ht2
  haveI : T1Space (Mx D m n) := @T2Space.t1Space _ _ ht2
  haveI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩

theorem poinX_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  intro D ψ hψ S S₀ T ρ d β hβ
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank S.rank
  haveI : IsTopologicalAddGroup (WO S T) := hg
  haveI : LocallyCompactSpace (WO S T) := hlc
  obtain ⟨hg', -, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'
  have hjX : Continuous fun u : WO S T => u ⬝ d.jX := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hjY : Continuous fun u : WO S T => u ⬝ d.jY := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T =>
      ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ) := by
    intro γ
    have e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) =
        fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY)) :=
      funext fun u => (d.symplOH_extX_extY T _ _).symm
    have hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY)) := by
      rw [e]
      refine GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_
      · simp only [HypDec.extX_apply]
        exact (hjX.add continuous_const).matrix_mul continuous_const
      · simp only [HypDec.extY_apply]
        exact hjY.matrix_mul continuous_const
    exact (hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
  have hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U)) :=
    (hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))
  have hF := finite_rat_mem_of_isCompact _ hK
  have vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0 := by
    intro u hu γ hγ
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)
  refine (continuous_finsetSum hF.toFinset fun γ _ => hterm γ).continuousAt.congr
    (Filter.eventually_of_mem hUn fun u hu => ?_)
  show _ = poinX ψ d T β u
  unfold poinX
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  rw [vanish u hu γ hγ, mul_zero]

end GlobalTheory.BumpMix

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBumpStatement

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix


theorem _root_.GlobalTheory.T.continuous_poincareSumOverRationalHom_bump : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  first | exact @GlobalTheory.BumpMix.poinX_continuous | exact GlobalTheory.BumpMix.poinX_continuous | (intros; apply GlobalTheory.BumpMix.poinX_continuous <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCore

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixQuasi

variable {D : D7}

theorem pair_add_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x + x') a) = trHalf D (pairS T x a) + trHalf D (pairS T x' a) := by
  rw [← map_add (f := _)]
  congr 1
  simp only [pairS, Matrix.mul_add, trace_add]

theorem pair_add_right (T : HSp D) {ρ : ℕ} (x a a' : Mx D T.rank ρ) :
    trHalf D (pairS T x (a + a')) = trHalf D (pairS T x a) + trHalf D (pairS T x a') := by
  rw [← map_add (f := _)]
  congr 1
  simp only [pairS, adj_add, Matrix.add_mul, trace_add]

theorem pair_sub_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x - x') a) = trHalf D (pairS T x a) - trHalf D (pairS T x' a) := by
  rw [eq_sub_iff_add_eq, ← pair_add_left, sub_add_cancel]

theorem pair_rat {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) {x a : Mx D T.rank ρ}
    (hx : x ∈ ratMx D T.rank ρ) (ha : a ∈ ratMx D T.rank ρ) :
    ∃ c, trHalf D (pairS T x a) = algebraMap D.host.F (AF D.host.F) c := by
  rw [← d.symplOH_extX_extY]
  exact (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ (ratMx_mul hx (rat_mem _)) _ (ratMx_mul ha (rat_mem _))

theorem symplOH_coords {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (h0 : S₀.rank = 0) (u w : WO S T) :
    symplOH S T u w = trHalf D (pairS T (u ⬝ d.jX) (w ⬝ d.jY)) - trHalf D (pairS T (w ⬝ d.jX) (u ⬝ d.jY)) := by
  have hz : ∀ v : WO S₀ T, v = 0 := fun v => by
    funext i j
    exact absurd j.2 (by omega)
  have e : ∀ v : WO S T, v = d.extX T (v ⬝ d.jX) + d.extY T (v ⬝ d.jY) := fun v => by
    have h := eq_coords d v
    rwa [hz (v ⬝ d.j0), map_zero, add_zero] at h
  conv_lhs => rw [e u, e w]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, d.symplOH_extX_extY, symplOH_Y_X]
  ring

theorem poinX_quasi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  intro D ψ hψ S S₀ T ρ d h0 β γ w
  obtain ⟨δ, hδ⟩ : (ratW T S γ : WO S T) ⬝ d.jX ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have hδ' : (ratW T S γ : WO S T) ⬝ d.jX = rat δ := hδ.symm
  have ha : (ratW T S γ : WO S T) ⬝ d.jY ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have eX : (ratW T S γ + w : WO S T) ⬝ d.jX = rat δ + w ⬝ d.jX := by
    rw [← hδ']; exact Matrix.add_mul _ _ _
  have eY : (ratW T S γ + w : WO S T) ⬝ d.jY = (ratW T S γ : WO S T) ⬝ d.jY + w ⬝ d.jY := Matrix.add_mul _ _ _
  rw [symplOH_coords T d h0, hδ']
  unfold poinX
  rw [eX, eY, ← (Equiv.subRight δ).tsum_eq, ← tsum_mul_left]
  generalize (ratW T S γ : WO S T) ⬝ d.jY = a at ha ⊢
  generalize w ⬝ d.jX = x
  generalize w ⬝ d.jY = y
  congr 1
  funext g
  rw [Equiv.subRight_apply, rat_sub]
  have e1 : rat δ + x + (rat g - rat δ) = x + rat g := by abel
  have e2 : rat δ + x + 2 • (rat g - rat δ) = x + 2 • rat g - rat δ := by
    rw [two_smul, two_smul]; abel
  have e3 : x + 2 • rat g - rat δ = x + (rat g + rat g - rat δ) := by
    rw [two_smul]; abel
  obtain ⟨c, hc⟩ := pair_rat T d (((ratMx D T.rank ρ).sub_mem ((ratMx D T.rank ρ).add_mem (rat_mem g) (rat_mem g))
    (rat_mem δ))) ha
  have e4 : trHalf D (pairS T (x + 2 • rat g - rat δ) (a + y)) =
      algebraMap D.host.F (AF D.host.F) c + (-(trHalf D (pairS T (rat δ) y) - trHalf D (pairS T x a)) +
        trHalf D (pairS T (x + 2 • rat g) y)) := by
    rw [pair_add_right, pair_sub_left T _ _ y, e3, pair_add_left T x _ a, hc]
    ring
  rw [e1, e2, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.1.2.2.1 c]
  ring

end GlobalTheory.BumpMixQuasi

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCoreStatement

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix


theorem _root_.GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  first | exact @GlobalTheory.BumpMixQuasi.poinX_quasi | exact GlobalTheory.BumpMixQuasi.poinX_quasi | (intros; apply GlobalTheory.BumpMixQuasi.poinX_quasi <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCore

section

namespace I195MixedCoordinates_857711241bb3adcbae71fb38

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_857711241bb3adcbae71fb38

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

theorem coreA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (H Z T : HSp D) (ρ : ℕ) (dH : HypDec H Z ρ), Z.rank = 0 → ∀ (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ f, IsThetaFunO ψ H T f ∧ ∀ x, (_root_.I195MixedCoordinates_857711241bb3adcbae71fb38.source dH) T ψ v.μ v.𝓕 f x 0 = β x := by
  intro D ψ hψ H Z T ρ dH hZ v β hβ
  exact ⟨poinX ψ dH T β, ⟨GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore D ψ hψ H Z T ρ dH hZ β, GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core D ψ hψ H Z T ρ dH hZ β hβ,
    GlobalTheory.T.continuous_poincareSumOverRationalHom_bump D ψ hψ H Z T ρ dH β hβ, GlobalTheory.T.contDiff_poincareSumOverRationalHom_realDirections D ψ hψ H Z T ρ dH β hβ⟩, GlobalTheory.T.mixedCoordinate_poincareSum_halfWitt_eq_bump D ψ hψ H Z T ρ dH v β hβ⟩

theorem bump_mul_theta_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, (_root_.I195MixedCoordinates_857711241bb3adcbae71fb38.source d) T ψ v.μ v.𝓕 Φ x = β x • g := by
  intro D ψ hψ S S₀ T ρ d v β g hβ hg
  let P : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral ρ
  let dH : HypDec (GlobalTheory.Doubling.dblSp P) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) ρ := GlobalTheory.Core.Rk.SWLaw.dblDec P
  have hZ : (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank = 0 := rfl
  obtain ⟨fH, hfH, hmix⟩ := coreA D ψ hψ _ _ T ρ dH hZ v β hβ
  refine ⟨_, isThetaFunO_prod 1 d.i₀ 1 (GlobalTheory.TowerSurj.embMat d dH) (GlobalTheory.TowerSurj.symplOH_split d dH T hZ) hg hfH,
    fun x => ?_⟩
  funext w₀
  have hz : ∀ z : WO (GlobalTheory.Core.Rk.SWLaw.zeroSp D) T, z = 0 := fun z => Matrix.ext fun _ j => by
    haveI : IsEmpty (Fin (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank) := by rw [hZ]; infer_instance
    exact isEmptyElim j
  have e2 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) =
      dH.extY T a + dH.extX T x + dH.ext0 T 0 := by
    intro a
    have hX : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jX = x := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jX, coord_jX]
    have hY : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jY = a := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jY, coord_jY]
    have h0 := hz (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.j0)
    rw [eq_coords dH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀)), hX, hY, h0]
    abel
  have e1 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat d.i₀) (d.extY T a + d.extX T x + d.ext0 T w₀) = w₀ := by
    intro a
    rw [sandwich_apply, rat_one, Matrix.one_mul]
    exact witt_extension_sum_mul_middle_coordinate d x a w₀
  have key : ∀ a : Mx D T.rank ρ,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 =
      g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 := by
    intro a
    rw [d.integrandS_eq, dH.integrandS_eq, symplOH_Y_X, symplOH_Y_X]
    show _ * (g _ * fH _) = _
    rw [e1, e2]
    ring
  have h2 : ∫ a in v.𝓕, heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 ∂v.μ =
      β x := hmix x
  change ∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 ∂v.μ = β x * g w₀
  rw [show (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0) =
      fun a => g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 from funext key,
    integral_const_mul, h2, mul_comm]

end GlobalTheory.BumpMix

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement

section

namespace I195MixedCoordinates_e9b37737007d4cfbb59b997f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_e9b37737007d4cfbb59b997f

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, (_root_.I195MixedCoordinates_e9b37737007d4cfbb59b997f.source d) T ψ v.μ v.𝓕 Φ x = β x • g := by
  first | exact @GlobalTheory.BumpMix.bump_mul_theta_mixS | exact GlobalTheory.BumpMix.bump_mul_theta_mixS | (intros; apply GlobalTheory.BumpMix.bump_mul_theta_mixS <;> assumption)
end
end
