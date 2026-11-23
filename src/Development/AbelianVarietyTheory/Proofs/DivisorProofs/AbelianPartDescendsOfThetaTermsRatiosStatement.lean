module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstantStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnit
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRoot

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  exact ⟨1, fun j hj V₁ _ _ _ hV hunit =>
    GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit n hn hodd j hj V₁ hV (hunit n hn.ne_zero)⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRootStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.thetaConst_eq_lam_root_mul | exact GlobalTheory.USep.thetaConst_eq_lam_root_mul | (intros; apply GlobalTheory.USep.thetaConst_eq_lam_root_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.Poinc.Sep.ModelRatio

theorem main : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  intro g n hn hodd
  obtain ⟨j₀, hcore⟩ := GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root n hn hodd
  refine ⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩
  haveI : IsAlgClosed k₀ := hk₀
  have := t.ab.comm
  obtain ⟨ρ₀, hρ₀⟩ := D.P.rigid
  obtain ⟨w, hw⟩ := hL
  obtain ⟨ρ, hρ, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀
  let x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) :=
    fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1 := fun i => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1
    rw [← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K t.pol ρ hρ (n ^ j) _ x v hx hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP
  have hgen := GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg
  obtain ⟨M, lam, hM, hval⟩ := hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen
  have up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀) := fun i => by
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)
    have q := GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)
    rw [hi] at q
    exact hval y (v i) q
  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  obtain ⟨c₀, ζ, hζ, hva⟩ := up a
  obtain ⟨c₀', ζ', hζ', hva'⟩ := up a'
  obtain ⟨s₁, hs₁, hs₁e⟩ := hrat 0 c₀ c₁ hc₁
  obtain ⟨s₂, hs₂, hs₂e⟩ := hrat 0 c₀' c₁ hc₁
  have hζk : ζ ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
  have hζk' : ζ' ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)
  rw [hva', hs₂e] at hne
  have h₁ : ζ' * s₂ ≠ 0 := fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)
  refine ⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩
  rw [hva, hva', hs₁e, hs₂e]
  have e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) =
      ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁)) := by ring
  rw [e₁, inv_mul_cancel₀ h₁]
  ring

end GlobalTheory.Poinc.Sep.ModelRatio
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  first | exact @GlobalTheory.Poinc.Sep.ModelRatio.main | exact GlobalTheory.Poinc.Sep.ModelRatio.main | (intros; apply GlobalTheory.Poinc.Sep.ModelRatio.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep.DescentBaseChange

theorem unitS_subfield {K : Type} [Field K] (k₀ : Subfield K) (u : k₀ˣ) :
    ZM.unitS (spMap k₀.subtype ≫ spMap (RingHom.id k₀)) u = unitOn (Units.map k₀.subtype.toMonoidHom u) := by
  ext
  simp only [ZM.unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (k₀.subtype.comp (RingHom.id k₀)))
  exact (congrArg (fun f => f.hom (u : k₀)) this).symm

theorem tObj_of_baseChange : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (N : ℕ), (N : K) ≠ 0 → ∀ (J : Type) (b : ZM.TBase k₀ N), ∃ (t : ZM.TObj D.P.g N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀))) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
  intro V₁ _ _ D K _ _ ev k₀ N hN J b
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨P, φ, hφ, hg, hm, w, hw⟩ := L1.polBaseChange _ _ (spMap ev) D.P
  have hpb : IsGrpPullback P.A D.P.A (spMap ev) φ := by
    refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl
  let ze : Kˣ := Units.map k₀.subtype.toMonoidHom b.ζ
  have hze : IsPrimitiveRoot ze N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K k₀.subtype)
  obtain ⟨pt, hpt, hpw⟩ := GlobalTheory.EllipticLevel.exists_symplectic_system L1 P N hN ze hze
  have hu := unitS_subfield k₀ b.ζ
  have key : ∀ g', P.g = g' → ∃ (t : ZM.TObj g' N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀)))
      (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
    rintro _ rfl
    exact ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
             ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := hpt
             bij := GlobalTheory.symplectic_system_torsion_basis L1 K P N ze pt hN hze hpt hpw
             pairing := hu ▸ hpw
             act := fun _ => 𝟙 _, hom := fun _ => inferInstance }, φ, hpb, LBIso.symm ⟨w, hw⟩⟩
  exact key _ hg

theorem tBase_of_isAlgClosed (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharZero k₀] (N : ℕ) (hN : N ≠ 0) : Nonempty (ZM.TBase k₀ N) := by
  haveI : NeZero (N : k₀) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N k₀)
    (Polynomial.degree_cyclotomic_pos N k₀ (Nat.pos_of_ne_zero hN)).ne'
  have hp : IsPrimitiveRoot z N := (Polynomial.isRoot_cyclotomic_iff).1 hz
  exact ⟨⟨(hp.isUnit (Nat.pos_of_ne_zero hN).ne').unit, (Nat.cast_ne_zero.2 hN : (N : k₀) ≠ 0).isUnit,
    fun K _ β => hp.map_of_injective β.injective⟩⟩

theorem polarised_part_model : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  intro g n hn hodd
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points L1 L2 g Empty (fun x => x.elim) 0 n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield g n hn hodd
  refine ⟨max (max j₁ j₂) 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hDg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hu
  have hj1 : j₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hK : ∀ m : ℕ, m ≠ 0 → (m : K) ≠ 0 := fun m hm => by
    rw [← map_natCast ev]; exact ((hunit m hm).map ev).ne_zero
  haveI : CharZero k₀ := charZero_of_inj_zero fun m hm => by
    by_contra h
    exact hK m h (by simpa using congrArg k₀.subtype hm)
  have hN0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  obtain ⟨b⟩ := tBase_of_isAlgClosed k₀ ((n ^ j) ^ 2) hN0
  obtain ⟨t, π₁, hπ, hL⟩ := tObj_of_baseChange V₁ D K ev k₀ ((n ^ j) ^ 2) (hK _ hN0) Empty b
  subst hDg
  obtain ⟨v, hv⟩ := ZM.TObj.exists_hasTh_of_isLocalRing L1 L2 (hodd.pow) t
  have hspan := ZM.FamilyScheme.span_theta L1 L2 t n v hn.two_le (dvd_pow_self n (by omega)) hv
  obtain ⟨a', ha'⟩ : ∃ a', v a' ≠ 0 := by
    by_contra h
    push_neg at h
    have : Set.range v ⊆ {0} := by rintro _ ⟨a, rfl⟩; exact h a
    rw [Ideal.span_eq_bot.2 (fun x hx => this hx)] at hspan
    exact bot_ne_top hspan
  have hr := hj₂ j hj2 V₁ hCN hunit D rfl X C e u mo hmo hT K ev k₀ hk₀ hu k₀ Empty b _ t π₁ hπ hL v hv
  choose r hrk hr using fun a => hr a a' ha'
  let w : ZM.Ix D.P.g ((n ^ j) ^ 2) → k₀ := fun a => ⟨r a, hrk a⟩
  have hw : t.HasTh (𝟙 _) (fun a => k₀.subtype (w a)) :=
    GlobalTheory.GenericObject.hasTh_unit_mul t _ v _ (v a')⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero ha')) (fun a => by
      show r a = (v a')⁻¹ * v a
      rw [hr a, mul_comm (r a), ← _root_.mul_assoc, inv_mul_cancel₀ ha', _root_.one_mul]) hv
  have hd : ZM.VeryDense (ZM.objPrimes b (fun x : Empty => x.elim) 0 (RingHom.id k₀) w) := by
    intro q f hq hf
    have hq0 : q = ⊥ := by
      rcases Ideal.eq_bot_or_top q with h | h
      · exact h
      · exact absurd h hq.ne_top
    subst hq0
    exact ⟨⊥, ⟨K, inferInstance, inferInstance, k₀.subtype, t, (RingHom.injective_iff_ker_eq_bot _).1 k₀.subtype_injective,
      fun x => x.elim, hw⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, -, hmap⟩ := hj₁ j hj1 k₀ b k₀ (RingHom.id k₀) w hd
  obtain ⟨φ, hφ, hφL, -, -⟩ := hmap K k₀.subtype t (fun x => x.elim) hw
  obtain ⟨w', hw'⟩ := LBIso.trans (pull_isLB D.P.isLB π₁) t.isLB (pull_isLB t₀.isLB φ) (LBIso.symm hL) hφL
  exact ⟨t₀.A, inferInstance, t₀.ab.comm, t₀.L, t.A, inferInstance, π₁, φ, w', t₀.ab, t₀.isLB, hπ, hφ, hw'⟩

end GlobalTheory.USep.DescentBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.polarisedAbelianPart_model_over_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  first | exact @GlobalTheory.USep.DescentBaseChange.polarised_part_model | exact GlobalTheory.USep.DescentBaseChange.polarised_part_model | (intros; apply GlobalTheory.USep.DescentBaseChange.polarised_part_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatios

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem descAt_of_thetaTerms : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  intro g n hn hodd
  obtain ⟨j₁, h₁⟩ := GlobalTheory.T.polarisedAbelianPart_model_over_subfield g n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel g n hn hodd
  refine ⟨max j₁ j₂, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨B₀, iG₀, iC₀, M₀, B', iG', π₁, π₀, w, hA, hM, hp1, hp0, hw⟩ :=
    h₁ j (le_trans (le_max_left _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
  have hP := h₂ j (le_trans (le_max_right _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
    B₀ M₀ B' π₁ π₀ w hA hM hp1 hp0 hw
  have hsq : ∀ a : D.X, (spMap ev ≫ (D.c a).left) ≫ D.P.A.hom = 𝟙 (Sp K) ≫ spMap ev := by
    intro a
    rw [Category.assoc, Over.w (D.c a)]
    simp
  let c' : D.X → (Sp K ⟶ B'.left) := fun a => hp1.1.lift (spMap ev ≫ (D.c a).left) (𝟙 _) (hsq a)
  have hc1 : ∀ a, c' a ≫ B'.hom = 𝟙 _ := fun a => hp1.1.lift_snd _ _ _
  have hc2 : ∀ a, c' a ≫ π₁ = spMap ev ≫ (D.c a).left := fun a => hp1.1.lift_fst _ _ _
  choose c₀ hc₀ using fun a => hP a (c' a) (hc1 a) (hc2 a)
  exact ⟨B₀, iG₀, iC₀, M₀, c₀, B', iG', π₁, π₀, w, c', hA, hM, hp1, hp0, hw, fun a => ⟨hc1 a, hc2 a, (hc₀ a).symm⟩⟩

end GlobalTheory.USep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatiosStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  first | exact @GlobalTheory.USep.descAt_of_thetaTerms | exact GlobalTheory.USep.descAt_of_thetaTerms | (intros; apply GlobalTheory.USep.descAt_of_thetaTerms <;> assumption)
end
end
