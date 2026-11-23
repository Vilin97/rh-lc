module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneBF_red_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have h1 : InK B.V LV (· = v) 1 := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y _
    simp
  have hfix : s.om (1, κ) f = f :=
    GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (fun w hw => hw ▸ ⟨hG.tame, hU.1, hU.2⟩) f hf 1 κ h1 hκ
  have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ f hf.1
  have hsplit : s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f =
      s.om (1, n * J.d.emb0 γ) (s.om (1, J.d.levi t) f) := by
    have : n * J.d.levi t * J.d.emb0 γ * κ = (n * J.d.emb0 γ) * J.d.levi t * κ := by
      rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
      simp only [mul_assoc]
    rw [this]
    have e : ((1 : GA D B.V), (n * J.d.emb0 γ) * J.d.levi t * κ) =
        ((1, n * J.d.emb0 γ) * (1, J.d.levi t)) * (1, κ) := by
      simp
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix]
  intro h0
  apply hne
  rw [hsplit, h𝔉.equiv _ hg n hnN hnG γ hγ, h0]
  have : opA ψ J.d B.o B.ζ s.om₀ n γ 0 = 0 := by
    funext w
    simp [opA, jacT, heisO]
  rw [this, smul_zero]

end GlobalTheory.FinPl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  first | exact @GlobalTheory.FinPl.oneBF_red_torus | exact GlobalTheory.FinPl.oneBF_red_torus | (intros; apply GlobalTheory.FinPl.oneBF_red_torus <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  first | exact @GlobalTheory.FinPl.VacFlat.flat_vac | exact GlobalTheory.FinPl.VacFlat.flat_vac | (intros; apply GlobalTheory.FinPl.VacFlat.flat_vac <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem inK_mul {D : D7} (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S) :
    InK S L P a → InK S L P b → InK S L P (a * b) := by
  rintro ⟨ha, hma⟩ ⟨hb, hmb⟩
  refine ⟨(grpAt S P).mul_mem ha hb, ?_⟩
  intro y hy
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := by
    intro i
    have : (mt S b *ᵥ y) i = ∑ j, mt S b i j * y j := rfl
    rw [this]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hmul : mt S (a * b) = mt S a * mt S b := rfl
  rw [hmul, ← Matrix.mulVec_mulVec]
  exact (hmb y hy).trans (hma _ hy')

end GlobalTheory.FinPl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S), InK S L P a → InK S L P b → InK S L P (a * b) := by
  first | exact @GlobalTheory.FinPl.inK_mul | exact GlobalTheory.FinPl.inK_mul | (intros; apply GlobalTheory.FinPl.inK_mul <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvStep.inv_int | exact GlobalTheory.FinPl.InvStep.inv_int | (intros; apply GlobalTheory.FinPl.InvStep.inv_int <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := by
  first | exact @GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | exact GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | (intros; apply GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  first | exact @GlobalTheory.FinPl.LeviUnitK.inK_levi | exact GlobalTheory.FinPl.LeviUnitK.inK_levi | (intros; apply GlobalTheory.FinPl.LeviUnitK.inK_levi <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneCosetBF : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf
  refine ⟨GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf, ?_⟩
  intro h hh hne
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.T.iwasawa_decomposition_selfDual_wittSplit_at_place D J.W J.W₀ ρ J.d LW LW₀ v hG.tame hG.sdW hG.sdW₀ hG.monoW h hh
  have h1 := GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have hinv := GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hrat := GlobalTheory.T.torusEntryRatio_integral_at_unramified_place D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hlast := GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hint := GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place D ρ v t ht hinv hrat hlast
  have hK := GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * J.d.emb0 γ, ?_, ?_, J.d.levi t * κ, GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem D J.W LW (· = v) _ _ hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt D J.W J.W₀ ρ J.d (· = v) γ hγ)
  · rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobiStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.oneCoset_besselToFourierJacobi : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  first | exact @GlobalTheory.FinPl.oneCosetBF | exact GlobalTheory.FinPl.oneCosetBF | (intros; apply GlobalTheory.FinPl.oneCosetBF <;> assumption)
end
end
