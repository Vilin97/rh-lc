module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjectiveStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HdRFibre



theorem fibre_baseChange : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  intro C₀ _ _ A₀ _ _ hA O _ a
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ A₀ hA
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))
  have hbc := (hBC C₀ A₀ g hA hg (IsLocalRing.ResidueField C₀) _ _ hh).1
  obtain ⟨hfin, hproj, -⟩ := hFree.prim hA hg
  haveI := Module.finitePresentation_of_projective C₀ (primDR A₀)
  haveI : Module.Free C₀ (primDR A₀) := Module.free_of_flat_of_isLocalRing
  refine ⟨hbc.bcMap, ?_, ?_, ?_⟩
  · intro h'
    let l : primDR A₀ →ₗ[C₀] IsLocalRing.ResidueField C₀ :=
      { toFun c := h' ((Published.AbelianDeRham.bcMor hh).pull c)
        map_add' c d := by rw [map_add (f := _), map_add (f := _)]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh', hhl⟩ := Module.projective_lifting_property (Algebra.linearMap C₀ (IsLocalRing.ResidueField C₀)) l
      IsLocalRing.residue_surjective
    exact ⟨hh', hbc.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc := hbc.corr_iff.2 hx
    refine GlobalTheory.CrysFree.mem_smul_top_of_forall _ x fun c ↦ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hc c).symm.trans (LinearMap.zero_apply _)
  · intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)

end GlobalTheory.HdRFibre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

theorem _root_.GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  first | (exact @GlobalTheory.HdRFibre.fibre_baseChange) | (exact GlobalTheory.HdRFibre.fibre_baseChange) | (intros; apply GlobalTheory.HdRFibre.fibre_baseChange  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_crystal_reduction_squareZero_artinian : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  first | exact @GlobalTheory.CrysRed.exists_crysRed | exact GlobalTheory.CrysRed.exists_crysRed | (intros; apply GlobalTheory.CrysRed.exists_crysRed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  first | exact @GlobalTheory.CrysProj.hdR_projective | exact GlobalTheory.CrysProj.hdR_projective | (intros; apply GlobalTheory.CrysProj.hdR_projective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegers

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSummand

private theorem comp_mem_ker_smul_top
    {C C₀ k : Type} [CommRing C] [CommRing C₀] [IsLocalRing C₀] [CommRing k]
    {π : C →+* C₀} (hπ : Function.Surjective π) (q : C₀ →+* k)
    (hq : ∀ c ∈ IsLocalRing.maximalIdeal C₀, q c = 0)
    {H M V : Type 1} [AddCommGroup H] [Module C H]
    [AddCommGroup M] [Module C₀ M] [AddCommGroup V] [Module k V]
    (red : H →ₛₗ[π] M) (f : M →ₛₗ[q] V) (hsurj : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C H))
    (fker : ∀ y, f y = 0 → y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ M))
    (h : H) (hh : f (red h) = 0) :
    h ∈ RingHom.ker (q.comp π) • (⊤ : Submodule C H) := by
  let N : Submodule C H := RingHom.ker (q.comp π) • (⊤ : Submodule C H)
  have lift (y : M) (hy : y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ M)) :
      ∃ x ∈ N, red x = y := by
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro c hc y _
      obtain ⟨b, rfl⟩ := hπ c
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨b • x, Submodule.smul_mem_smul (RingHom.mem_ker.2 (hq (π b) hc))
        Submodule.mem_top, red.map_smulₛₗ b x⟩
    · rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
      exact ⟨x + x', N.add_mem hx hx', red.map_add x x'⟩
  obtain ⟨x, hx, hxe⟩ := lift _ (fker _ hh)
  have hle : RingHom.ker π ≤ RingHom.ker (q.comp π) := fun b hb ↦
    RingHom.mem_ker.2 (show q (π b) = 0 by rw [RingHom.mem_ker.1 hb, map_zero])
  have hsub : h - x ∈ N :=
    Submodule.smul_mono_left hle (hker _ (by rw [map_sub, hxe, sub_self]))
  simpa only [sub_add_cancel] using N.add_mem hsub hx

-- Check the two tensor module presentations before specializing to the closed fibre.
private theorem fibre_projective_tensorModOf
    (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B)
    (a : OAct (𝓞 F) B) :
    letI := tensorModOf (act (dp0 k) (𝟙 _) a)
    Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR B) := by
  change @Module.Projective _ _ _ _ (tensorModule (dp0 k) (𝟙 _) a)
  exact GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F k B hB a

theorem crys_projective : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  intro F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a
  have : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) * 1 ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul h1 h1
    rw [_root_.one_mul, hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  have : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  obtain ⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩ := GlobalTheory.T.exists_crystal_reduction_squareZero_artinian C C₀ π hπ hsq A₀ hA O a
  let a' : OAct (𝓞 F) A₀ :=
    { act := fun x ↦ a.act (algebraMap (𝓞 F) O x)
      hom := fun x ↦ a.hom _
      one := by rw [map_one]; exact a.one
      mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul]
      add := fun x y ↦ by rw [map_add (f := _), a.add] }
  obtain ⟨f, fsurj, fker, fequiv⟩ := GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'
  let q := algebraMap C₀ (IsLocalRing.ResidueField C₀)
  let B := (Over.pullback (spMap q)).obj A₀
  let aB : OAct (𝓞 F) B := OAct.pullback (spMap q) A₀ a'
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap q) A₀ hA
  let σ := q.comp π
  have hσ : Function.Surjective σ := IsLocalRing.residue_surjective.comp hπ
  have : RingHomCompTriple π q σ := ⟨rfl⟩
  let H := Crys (divided₂ hsq) (spMap π) A₀
  let ρ := (crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)
  let ρB := act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) aB
  have hq (c : C₀) (hc : c ∈ IsLocalRing.maximalIdeal C₀) : q c = 0 := by
    change algebraMap C₀ (IsLocalRing.ResidueField C₀) c = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff c).2 hc
  refine GlobalTheory.T.projective_tensor_of_fibre_projective'
    C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ H (HdR B)
    ρ ρB (f.comp red) hfin hproj (fsurj.comp hsurj) ?_ ?_
      (fibre_projective_tensorModOf F (IsLocalRing.ResidueField C₀) B hB aB)
  · exact comp_mem_ker_smul_top hπ q hq red f hsurj hker fker
  · intro x h
    exact (congrArg (fun y : HdR A₀ ↦ f y) (hequiv (algebraMap (𝓞 F) O x) h)).trans
      (fequiv x (red h))

end GlobalTheory.HTSummand
end
end
end
