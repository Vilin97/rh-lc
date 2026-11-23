module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValuedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCoordPtLocal

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory


noncomputable section
namespace GlobalTheory.CoordReduce



open ReciprocityTheory.ChartRestriction.G.Out in
theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

end GlobalTheory.CoordReduce
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportional

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportionalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polAV_point_defined_over_of_coords_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 → ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K) (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K), GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) → (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  first | exact @GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | exact GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | (intros; apply GlobalTheory.Poinc.Sep.defOver_of_coord_proportional <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem points_defOver : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  intro g n hn hodd
  obtain ⟨j₁, hC⟩ := GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued g n hn hodd
  refine ⟨max j₁ 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat B₀ _ _ M₀ B' _ π₁ π₀ w hB₀ hM₀ h₁ h₀ hw a x hx hxa
  have hj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ j := Nat.pow_le_pow_right hn.pos hj1)
  have hmK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have h := (hunit (n ^ j) (by positivity)).map ev
    rw [map_natCast] at h
    exact h.ne_zero
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsCommMonObj D.P.A := D.P.isAb.comm
  haveI : IsCommMonObj B' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₁
  let P' : PolAV (Sp K) :=
    { A := B'
      isAb :=
        { comm := inferInstance
          smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 D.P.isAb.smooth
          proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 D.P.isAb.proper
          geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 D.P.isAb.geomConnected }
      g := D.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h₁.1 D.P.smoothDim
      L := D.P.L.pull π₁
      isLB := pull_isLB D.P.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull h₁ D.P.rigid
      sym := GlobalTheory.PolBaseChange.sym_pull h₁ D.P.sym
      ample := by
        haveI := D.P.isAb.proper
        exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback D.P.isLB D.P.ample h₁.1
      ktriv := kTriv_pull h₁ D.P.isLB (pull_isLB D.P.isLB _)
        ((isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl (pull_isLB D.P.isLB π₁))) D.P.ktriv }
  have hw' : LBIso P'.L (M₀.pull π₀) := ⟨w, hw⟩
  have hSym : Out.Sym B₀ M₀ := (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend k₀ K k₀.subtype B₀ B' π₀ M₀ P'.L hB₀ h₀
    hM₀ P'.isLB hw').2.1 P'.sym
  have h₀' : IsGrpPullback P'.A B₀ (spMap (algebraMap k₀ K)) π₀ := h₀
  set_option synthInstance.maxHeartbeats 400000 in
  have : Flat (spMap k₀.subtype) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  let P₀ : PolAV (Sp k₀) :=
    { A := B₀, isAb := hB₀, g := P'.g,
      smoothDim := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre k₀ K k₀.subtype B₀ P'.A.left π₀ P'.A.hom P'.g hB₀ h₀.1
        P'.smoothDim,
      L := M₀, isLB := hM₀, rigid := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local M₀ hM₀ _ _, sym := hSym,
      ample := GlobalTheory.AmpleDescent.relAmple_of_faithfullyFlat k₀ K B₀ P'.A π₀ M₀ P'.L hB₀ h₀' hM₀ P'.isLB hw' P'.ample,
      ktriv := GlobalTheory.AmpleDescent.kTriv_of_pull h₀ hM₀ P'.isLB hw' P'.ktriv }
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := B₀) (G' := B') h₀
    (𝟙 (Sp K)) (spMap k₀.subtype) (Category.id_comp _)
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := D.P.A) (G' := B') h₁
    (𝟙 (Sp K)) (spMap ev) (Category.id_comp _)
  let t₀ : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let t₁ : Sp K ⟶ Sp V₁ := spMap ev
  let Ix := {y : Over.mk t₀ ⟶ B₀ // y ^ (n ^ j) ^ 2 = 1}
  let X' : Ix → (baseOver (Sp K) ⟶ B') := fun i => Φ₀.symm i.1
  have hX' : ∀ i, X' i ^ (n ^ j) ^ 2 = 1 := fun i => Φ₀.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, i.2, map_one])
  let z' : baseOver (Sp K) ⟶ B' := Over.homMk x hx
  let yD : Ix → (Over.mk t₁ ⟶ D.P.A) := fun i => Φ₁ (X' i)
  have hyD : ∀ i, yD i ^ (n ^ j) ^ 2 = 1 := fun i => by
    simp only [yD]; rw [← map_pow, hX' i, map_one]
  have hzD : (Φ₁ z').left = t₁ ≫ (D.c a).left := by
    rw [hΦ₁]; simp [t₁, z', hxa]
  obtain ⟨vD, l, r, hvD, hr, hvr⟩ := hC j hj₁ V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hrat
    Ix yD hyD a (Φ₁ z') hzD
  have HD := GlobalTheory.FullExtend.isCoordPt_move (f := spMap ev) (T := baseOver (Sp K)) (T₀ := Over.mk t₁) (𝟙 _)
    (P₀ := D.P) (P := P') (φ := π₁) h₁ (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.P.isLB π₁)) (B := Over.mk t₁)
    (𝟙 _) (𝟙 _) (by simp) (by simp [t₁])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS D.P.isLB (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := yD)
    (fun i => (Category.id_comp _).trans (hΦ₁ _)) hX' (z := z') (z₀ := Φ₁ z') ((Category.id_comp _).trans (hΦ₁ z')) hvD
  obtain ⟨v₀, hv₀⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp k₀) P₀ t₀ (n ^ j)
    hmodd hmK Ix (fun i => i.1) (fun i => i.2)).1 (Φ₀ z')
  have H0 := GlobalTheory.FullExtend.isCoordPt_move (f := spMap k₀.subtype) (T := baseOver (Sp K)) (T₀ := Over.mk t₀) (𝟙 _)
    (P₀ := P₀) (P := P') (φ := π₀) h₀ hw' (B := Over.mk t₀) (𝟙 _) (𝟙 _) (by simp) (by simp [t₀])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS hM₀ (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := fun i => i.1)
    (fun i => (Category.id_comp _).trans ((congrArg Over.Hom.left (Φ₀.apply_symm_apply i.1)).symm.trans (hΦ₀ _)))
    hX' (z := z') (z₀ := Φ₀ z') ((Category.id_comp _).trans (hΦ₀ z')) hv₀
  have HD' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (vD i)) := by
    convert HD using 2 with i
    simp
  have H0' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (v₀ i)) := by
    convert H0 using 2 with i
    simp
  obtain ⟨-, U₂, -, -⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp K) P' (𝟙 _)
    (n ^ j) hmodd hmK Ix X' hX'
  obtain ⟨c, hc⟩ := (U₂ z' v₀ vD H0').1 HD'
  have hv₀r : ∀ i, v₀ i = ((c⁻¹ : Kˣ) * l) * r i := fun i => by
    have := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [_root_.mul_assoc, ← hvr i, this, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hD := GlobalTheory.T.polAV_point_defined_over_of_coords_proportional K k₀ hk₀ P₀ (n ^ j) hmodd hm3 hmK (Φ₀ z') v₀ _ r hv₀ hr hv₀r
  rwa [hΦ₀] at hD

end GlobalTheory.USep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  first | exact @GlobalTheory.USep.points_defOver | exact GlobalTheory.USep.points_defOver | (intros; apply GlobalTheory.USep.points_defOver <;> assumption)
end
end
