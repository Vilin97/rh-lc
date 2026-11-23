module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  first | exact @GlobalTheory.HTSummand.crys_projective | exact GlobalTheory.HTSummand.crys_projective | (intros; apply GlobalTheory.HTSummand.crys_projective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual GlobalTheory.Published.GrothendieckMessing

namespace GlobalTheory.HTDefLift

theorem exists_crysForm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ φ₀ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ₀ ∧ (∀ φ, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → φ = φ₀) ∧ (∀ (c : D.O) x y, φ₀ (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x) y = φ₀ x (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (D.star c).unop y)) ∧ ∃ φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀, GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' ∧ ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr x x' → (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr y y' → φ' x' y' = π (φ₀ x y) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm CS o₀.isLB o₀.rig₁ o₀.rig₂
  refine ⟨φ₀, hφ₀, fun φ hφ ↦ hφ.unique CS o₀.isLB hφ₀, fun c x y ↦ ?_, ?_⟩
  · haveI := o₀.act.hom c
    haveI := o₀.act.hom (D.star c).unop
    have := hφ₀.adjoint CS o₀.isLB o₀.isLB hφ₀ (o₀.act.act c) (o₀.act.act (D.star c).unop) (LBIso.symm (o₀.rosati c)) x y
    exact this.symm
  · have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
      (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
        (by rw [GlobalTheory.CechPic.cls_pull o₀.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
    obtain ⟨φ', hφ', e'⟩ := hφ₀.pull o₀.isLB (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
      (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
    exact ⟨φ', hφ', e'⟩

end GlobalTheory.HTDefLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummand

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  obtain ⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩ :=
    GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  haveI := hfin
  haveI := hproj
  obtain ⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩ := GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨hskew, hbij⟩ := GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀
  haveI : Nontrivial C₀ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have ht : RingHom.ker π = ⊤ := eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)
    rw [ht, ← Ideal.one_eq_top, one_pow] at hsq
    exact one_ne_zero hsq
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  have hlagr := GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'
  have hlie := GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀
  have hprojF := GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  let F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A) := (Fil o₀.A).comap red
  have hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]
    · rw [map_add (f := _), hx, hy, add_zero]
  have hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F := fun x hx ↦ by
    show red x ∈ Fil o₀.A
    rw [hredI x hx]; exact zero_mem _
  have hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F := by
    intro c x hx
    show red _ ∈ Fil o₀.A
    rw [hpush]
    haveI := o₀.act.hom c
    exact push_mem_Fil (o₀.act.act c) hx
  have hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π := by
    intro x hx y hy
    rw [RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact hlagr.1 _ hx _ hy
  have hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F := by
    intro x hx
    show red x ∈ Fil o₀.A
    refine hlagr.2 _ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := hsurj z
    rw [hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact RingHom.mem_ker.1 (hx y hz)
  have hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F := by
    refine le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_
    obtain ⟨d, hd, he⟩ := (hE' (red x)).1 hx
    have hx' : x = d + (x - d) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))
  have hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F),
        GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧
        d - ∑ i, w i ∈ F := by
    intro d hd
    have hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d)
        ∈ Fil o₀.A := hd
    rw [map_sub, LinearMap.map_smulₛₗ, hpush] at hd'
    obtain ⟨w₀, hw₀, hsum⟩ := hlie (red d) hd'
    choose w hw using fun i ↦ hsurj (w₀ i)
    refine ⟨w, fun i c ↦ ?_, ?_⟩
    · show red _ ∈ Fil o₀.A
      rw [map_sub, LinearMap.map_smulₛₗ, hpush, hw]
      exact hw₀ i c
    · show red _ ∈ Fil o₀.A

      rw [map_sub, map_sum]
      simp only [hw]
      exact hsum
  obtain ⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩ := GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR
    (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj
    F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie
  refine ⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd,
    fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ F := hy
    rw [← hEF] at hx
    obtain ⟨d, hd, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨d, hd, (hcorr _ _).2 (by rw [map_add (f := _), hredI j hj, add_zero])⟩
  · rw [← (hcorr d y).1 hc]
    have : d ∈ F := hEF ▸ Submodule.mem_sup_left hd
    exact this

end GlobalTheory.HTSummand
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummandStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  first | exact @GlobalTheory.HTSummand.exists_summand | exact GlobalTheory.HTSummand.exists_summand | (intros; apply GlobalTheory.HTSummand.exists_summand <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq' t o₀
  have hsq : RingHom.ker π ^ 2 = 0 := by rw [hsq']; rfl
  obtain ⟨tR, rfl⟩ : ∃ tR : R →+* C, t = spMap tR :=
    ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  obtain ⟨E, hEc, hEf, hEs, hEi, hEl⟩ := GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    ⟨{ φ := i
       φ₂ := φ₂
       cart := h
       sq := hsq2
       act := hact
       pol := hpol
       eta := e5 }⟩⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.obj_lift_sqZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  intro p _ D R _ b N _ hN A₁ A₀ _ _ _ _ π β hπ hk o
  have hc : spMap (π.comp β) = spMap π ≫ spMap β := by
    simp only [spMap, Sp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk2 : RingHom.ker π ^ 2 = ⊥ := by rw [pow_two]; exact hk
  revert o
  rw [hc]
  intro o
  first
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N hN A₁ A₀ π hπ hk2 (spMap β) o
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N A₁ A₀ π hπ hk2 (spMap β) o
end
end
