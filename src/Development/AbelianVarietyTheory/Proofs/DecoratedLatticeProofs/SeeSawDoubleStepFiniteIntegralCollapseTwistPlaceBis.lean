module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecondStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevelStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacobStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFir

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepCell.LeftOne

theorem vac_empty_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {LS : Lat S} {LT : Lat T} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => False) f) : Vac ψ S T LS LT (fun _ => False) (comb ψ S T e f) :=
  ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).2 LS LT f hf

theorem vac_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT (fun _ => False) f := by
  have h := (GlobalTheory.DisjComb.main D ψ hψ S T (fun _ => True) (fun _ => False) (fun _ _ h => h)).2.2.2.2 LS LT f hS hT
  have e : (fun p : Pl D => True ∨ False) = fun _ => True := by funext p; simp
  rw [e] at h
  exact (h.1 hf).2

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv _ hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ r hr q₁ q₂
  have s0 := hv.sd j (by omega)
  have s1 := hv.sd (j + 1) (by omega)
  have s2 := hv.sd (j + 1 + 1) (by omega)
  have t₁ := (vac_empty_comb hc.std (hv.atG j).1 (vac_empty_comb hc.std (hF.atQ j).1 (vac_empty hc.std s0 s1 h₁))).1
  have t₂ := (vac_empty_comb hc.std (hv.atG (j + 1)).1
    (vac_empty_comb hc.std (hF.atQ (j + 1)).1 (vac_empty hc.std s1 s2 h₂))).1
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  have key := (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ t₁ t₂ (φ α)
    (hv.ram j (φ α) (hφ α)).1 g q₁ q₂).1 r hr
  exact congrArg (fun z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ z (rTrans q₂ f)) key

end GlobalTheory.DStepCell.LeftOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFirStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

theorem _root_.GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepCell.LeftOne.main | exact GlobalTheory.DStepCell.LeftOne.main | (intros; apply GlobalTheory.DStepCell.LeftOne.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAwayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

theorem _root_.GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  first | exact @GlobalTheory.CellLevels.levels | exact GlobalTheory.CellLevels.levels | (intros; apply GlobalTheory.CellLevels.levels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotientStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_quotient_eq_integral_factor_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G G₁ G₂ R K₁ K₂ : Subgroup H), IsClosed (G : Set H) → IsClosed (G₁ : Set H) → IsClosed (G₂ : Set H) → IsClosed (R : Set H) → G₁ ≤ G → G₂ ≤ G → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → (∃ e : (G₁ × G₂) ≃ₜ G, ∀ p, (e p : H) = p.1 * p.2) → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R) → K₁ ≤ G₁ → K₂ ≤ G₂ → IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) → IsOpen ((K₁.subgroupOf G₁ : Subgroup G₁) : Set G₁) → IsOpen ((K₂.subgroupOf G₂ : Subgroup G₂) : Set G₂) → ∀ (ρ : Measure (R.subgroupOf G)) (μ : Measure G) (ρ₁ : Measure (R.subgroupOf G₁)) (μ₁ : Measure G₁), ρ.IsHaarMeasure → μ.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₁.IsHaarMeasure → ρ.IsInvInvariant → μ₁ {g | g.1 ∈ K₁} = 1 → ρ₁ {g | g.1.1 ∈ K₁} = 1 → ∀ (f : H → ℂ) (z : ℂ), (∀ r ∈ R, r ∈ G → ∀ g ∈ G, f (r * g) = f g) → (∀ k ∈ K₂, ∀ g ∈ G, f (g * k) = f g) → (∀ g ∈ G, f g ≠ 0 → ∃ r ∈ R, r ∈ G ∧ ∃ x ∈ G₁, ∃ k ∈ K₂, g = r * x * k) → IsQuotIntL1 ρ₁ μ₁ (fun x => f x.1) z → IsQuotIntL1 ρ μ (fun g => f g.1) (((μ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} / ρ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} : ℝ) : ℂ) * z) := by
  first | exact @GlobalTheory.CollapseFactor.collapse_factor | exact GlobalTheory.CollapseFactor.collapse_factor | (intros; apply GlobalTheory.CollapseFactor.collapse_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBesselStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∀ q₂ ∈ GfC (c.V (j + 1 + 1)), integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1 + 1), q₂ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSuppSecond.integ_support | exact GlobalTheory.DStepSuppSecond.integ_support | (intros; apply GlobalTheory.DStepSuppSecond.integ_support <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell



theorem cell_collapse : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  classical
  intro D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf z hz
  change Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) z at hz
  change Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) (v.kap j σ h * z)
  have hA1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hB := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC4 := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  set F := integ v w j σ h Ψ₁ Ψ₂ φ f with hFdef
  obtain ⟨f₁', hf₁', hinn⟩ := hz

  obtain ⟨-, hfc₁, -, -, -, hd₁⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, hfc₂, -, -, -, hd₂⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have invJ : (c.ρJ j (σ + 1) h).IsInvInvariant := (hd₁ _ _ (c.jac j (σ + 1) h).d).1.2.2 _ (hc.ρJ j (σ + 1) h)
  have invB : (c.ρB (j + 1 + 1) σ (idx_step h)).IsInvInvariant :=
    ((hd₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o).2.2 _ (hc.ρB _ _ _)
  obtain ⟨hQc₁, hQ'c₁, hQle₁, hQ'le₁, hcm₁, he₁, -, -, -, hR₁⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q
  obtain ⟨hQc₂, hQ'c₂, hQle₂, hQ'le₂, hcm₂, he₂, -, -, -, hR₂⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1 + 1)) w.Q
  have splitJ := (hR₁ _ _ (c.jac j (σ + 1) h).d).1
  have splitB := (hR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  have hJcl := GlobalTheory.jacGrp_isClosed D _ _ _ (c.jac j (σ + 1) h).d
  have hBcl := GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o

  obtain ⟨hJG₁, hJG₁c, hJG₁o⟩ := hv.JG (j + 1) (by omega)
  obtain ⟨hJG₂, hJG₂c, hJG₂o⟩ := hv.JG (j + 1 + 1) (by omega)
  obtain ⟨K₁, K₂, hK₁, hK₁Q, hK₂Q, hK₁c, hK₂c, hK₁o, hK₂o, hK₂, hKK⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₁ hJG₁c hJG₁o
  obtain ⟨K₁', K₂', hK₁', hK₁Q', hK₂Q', hK₁c', hK₂c', hK₁o', hK₂o', hK₂', hKK'⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1 + 1)) v.gP w.Q (v.JG (j + 1 + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₂ hJG₂c hJG₂o
  have hμ₁K : μ₁ {g | (g : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : grpAt (c.V (j + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁ g.1]
    exact hN₁.2.2.1
  have hρ₁K : ρ₁ {g | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (grpAt (c.V (j + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁ g.1.1]
    exact hN₁.2.2.2
  have hμ₂K : μ₂ {g | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁' g.1]
    exact hN₂.2.2.1
  have hρ₂K : ρ₂ {g | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁' g.1.1]
    exact hN₂.2.2.2

  have hinner : ∀ q₁ : grpAt (c.V (j + 1)) (· ∈ w.Q), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q₁.1 g.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * f₁' q₁) := by
    intro q₁
    have hl : ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o,
        r ∈ GfC (c.V (j + 1 + 1)) → ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (r * g) = F q₁.1 g :=
      fun r hr _ g _ => hC1 r hr q₁.1 g
    have hr : ∀ k ∈ K₂', ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (g * k) = F q₁.1 g := by
      intro k hk g _
      obtain ⟨κ, hκ, k', hk', rfl⟩ := (hK₂' k).1 hk
      rw [← mul_assoc, hC3 k' hk', hC2 κ hκ]
    have hs : ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 g ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d
        (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q),
        ∃ k ∈ K₂', g = r * y * k := by
      intro g hg hne
      obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hC4 q₁.1 q₁.2 g hg hne
      exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂' _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
    have H := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1 + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
      (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) K₁' K₂'
      hfc₂ hQc₂ hQ'c₂ hBcl hQle₂ hQ'le₂ hcm₂ he₂ splitB hK₁Q' hK₂Q' hK₁c' hK₂c' hK₁o' hK₂o'
      (c.ρB _ _ _) (c.μf _) ρ₂ μ₂ (hc.ρB _ _ _) (hc.μf _) hN₂.2.1 hN₂.1 invB hμ₂K hρ₂K (F q₁.1) (f₁' q₁) hl hr hs (hinn q₁)
    have e1 : {g : GfC (c.V (j + 1 + 1)) | ∃ a ∈ K₁', ∃ b ∈ K₂', (g : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1
    have e2 : {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (GfC (c.V (j + 1 + 1))) | ∃ a ∈ K₁', ∃ b ∈ K₂', ((g : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1.1
    rw [e1, e2] at H
    exact H

  haveI : LocallyCompactSpace (GfC (c.V (j + 1 + 1))) := hfc₂.locallyCompactSpace
  haveI := hc.μf (j + 1 + 1)
  haveI := hc.ρB (j + 1 + 1) σ (idx_step h)
  haveI := invB
  have hBcl' : IsClosed (((besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
      (GfC (c.V (j + 1 + 1))) : Subgroup _) : Set (GfC (c.V (j + 1 + 1)))) := hBcl.preimage continuous_subtype_val
  have huniq : ∀ (Φ : GfC (c.V (j + 1 + 1)) → ℂ) (z₁ z₂ : ℂ), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h))
      (c.μf (j + 1 + 1)) Φ z₁ → IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₂ → z₁ = z₂ :=
    fun Φ z₁ z₂ h1 h2 => IsQuotIntL1.unique hBcl' h1 h2

  have hex : ∀ q : GfC (c.V (j + 1)), ∃ z', IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q.1 g.1) z' := by
    intro q
    by_cases hq : ∃ q₂, F q.1 q₂ ≠ 0
    · obtain ⟨q₂, hq₂⟩ := hq
      obtain ⟨r, hr, -, y, hy, κ, hκ, k, hk, e⟩ := hB q.1 q.2 q₂ hq₂
      have e' : F q.1 = F y := funext fun q₂ => by rw [e, ← mul_assoc, hA3 k hk, hA2 κ hκ, hA1 r hr]
      exact ⟨_, by rw [e']; exact hinner ⟨y, hy⟩⟩
    · push_neg at hq
      refine ⟨0, ?_⟩
      have e : (fun g : GfC (c.V (j + 1 + 1)) => F q.1 g.1) = 0 := funext fun g => hq g.1
      rw [e]
      exact IsQuotIntL1.zero
  let fo : GA D (c.V (j + 1)) → ℂ := fun y => if hy : y ∈ GfC (c.V (j + 1)) then (hex ⟨y, hy⟩).choose else 0
  have hfo_spec : ∀ y (hy : y ∈ GfC (c.V (j + 1))), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F y g.1) (fo y) := by
    intro y hy
    have e : fo y = (hex ⟨y, hy⟩).choose := dif_pos hy
    rw [e]
    exact (hex ⟨y, hy⟩).choose_spec
  have hleft : ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) → ∀ g ∈ GfC (c.V (j + 1)), fo (r * g) = fo g := by
    intro r hr hrG g hg
    have e : F (r * g) = F g := funext fun q₂ => hA1 r hr g q₂
    have h1 := hfo_spec _ (mul_mem hrG hg)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hright : ∀ k ∈ K₂, ∀ g ∈ GfC (c.V (j + 1)), fo (g * k) = fo g := by
    intro k hk g hg
    have hkG : k ∈ GfC (c.V (j + 1)) := hQ'le₁ (hK₂Q hk)
    obtain ⟨κ, hκ, k', hk', e0⟩ := (hK₂ k).1 hk
    have e : F (g * k) = F g := funext fun q₂ => by rw [e0, ← mul_assoc, hA3 k' hk', hA2 κ hκ]
    have h1 := hfo_spec _ (mul_mem hg hkG)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hsupp : ∀ g ∈ GfC (c.V (j + 1)), fo g ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧
      ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ k ∈ K₂, g = r * y * k := by
    intro g hg hne
    have hq : ∃ q₂, F g q₂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have e : (fun g' : GfC (c.V (j + 1 + 1)) => F g g'.1) = 0 := funext fun g' => hcon g'.1
      have h0 := hfo_spec g hg
      rw [e] at h0
      exact huniq _ _ _ h0 IsQuotIntL1.zero
    obtain ⟨q₂, hq₂⟩ := hq
    obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hB g hg q₂ hq₂
    exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂ _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
  have hint : IsQuotIntL1 ρ₁ μ₁ (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1)
      (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    have e : (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) =
        v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) • f₁' := funext fun y => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact huniq _ _ _ (hfo_spec y.1 (hQle₁ y.2)) (hinner y)
    rw [e]
    exact hf₁'.smul _
  have Hout := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
    (jacGrp (c.jac j (σ + 1) h).d) K₁ K₂ hfc₁ hQc₁ hQ'c₁ hJcl hQle₁ hQ'le₁ hcm₁ he₁ splitJ hK₁Q hK₂Q hK₁c hK₂c hK₁o hK₂o
    (c.ρJ j (σ + 1) h) (c.μf _) ρ₁ μ₁ (hc.ρJ _ _ _) (hc.μf _) hN₁.2.1 hN₁.1 invJ hμ₁K hρ₁K fo _ hleft hright hsupp hint
  have e1 : {g : GfC (c.V (j + 1)) | ∃ a ∈ K₁, ∃ b ∈ K₂, (g : GA D (c.V (j + 1))) = a * b} =
      {g | g.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1
  have e2 : {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (GfC (c.V (j + 1))) |
      ∃ a ∈ K₁, ∃ b ∈ K₂, ((g : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) = a * b} =
      {g | g.1.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1.1
  rw [e1, e2] at Hout
  refine ⟨fun q => fo q.1, ?_, fun q => hfo_spec q.1 q.2⟩
  have ek : v.kap j σ h * z = v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    unfold VCom.kap; ring
  rw [ek]
  exact Hout

end GlobalTheory.DStepCell

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceBis

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  first | exact @GlobalTheory.DStepCell.cell_collapse | exact GlobalTheory.DStepCell.cell_collapse | (intros; apply GlobalTheory.DStepCell.cell_collapse <;> assumption)
end
end
